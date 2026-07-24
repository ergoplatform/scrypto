package scorex.crypto.authds.avltree.batch.serialization

import scorex.crypto.authds.avltree.batch.{BatchAVLProver, ProverLeaf, InternalProverNode, ProverNodes}
import scorex.crypto.authds.{ADValue, ADKey, Balance}
import scorex.crypto.hash.{CryptographicHash, Digest}
import scorex.util.encode.Base16
import scorex.utils.{Bytes, Ints, ByteArray, Logger}

import scala.util.Try

/**
  * Serializes and deserializes a [[BatchAVLProver]] tree into a manifest and subtrees.
  * The binary format is self-describing and includes length prefixes for variable-size subtrees.
  * Deserialization rejects malformed or inconsistent input by returning `Failure`.
  */
class BatchAVLProverSerializer[D <: Digest, HF <: CryptographicHash[D]]
    (implicit val hf: HF, val logger: Logger) { serializer =>

  private val labelLength = hf.DigestSize

  type SlicedTree = (BatchAVLProverManifest[D], Seq[BatchAVLProverSubtree[D]])

  /**
    * Slices an AVL tree into a top manifest and bottom subtrees at the given `subtreeDepth`.
    */
  def slice(tree: BatchAVLProver[D, HF], subtreeDepth: Int): SlicedTree = tree.topNode match {
    case tn: InternalProverNode[D] =>

      val height = tree.rootNodeHeight
      val rootProxyNode = ProxyInternalNode(tn)

      def getSubtrees(currentNode: ProverNodes[D],
                      currentHeight: Int,
                      parent: ProxyInternalNode[D]): Seq[BatchAVLProverSubtree[D]] = {
        currentNode match {
          case n: InternalProverNode[D] if currentHeight > subtreeDepth =>
            val nextParent = ProxyInternalNode(n)
            parent.setChild(nextParent)
            val leftSubtrees = getSubtrees(n.left, currentHeight - 1, nextParent)
            val rightSubtrees = getSubtrees(n.right, currentHeight - 1, nextParent)
            leftSubtrees ++ rightSubtrees
          case n: InternalProverNode[D] =>
            parent.setChild(ProxyInternalNode(n))
            Seq(BatchAVLProverSubtree(n.left), BatchAVLProverSubtree(n.right))
          case l: ProverLeaf[D] =>
            parent.setChild(l)
            Seq(BatchAVLProverSubtree(l))
        }
      }

      val subtrees = getSubtrees(tn.left, height - 1, rootProxyNode) ++ getSubtrees(tn.right, height - 1, rootProxyNode)
      val manifest = BatchAVLProverManifest[D](rootProxyNode, height)
      (manifest, subtrees)
    case l: ProverLeaf[D] =>
      (BatchAVLProverManifest[D](l, tree.rootNodeHeight), Seq.empty)
  }

  /**
    * Combines a manifest and its subtrees back into a single prover tree.
    */
  def combine(sliced: SlicedTree,
              keyLength: Int,
              valueLengthOpt: Option[Int]): Try[BatchAVLProver[D, HF]] = Try {
    val manifest = sliced._1
    manifest.root match {
      case tn: InternalProverNode[D] =>

        // manifest being mutated here
        def mutateLoop(n: ProverNodes[D]): Unit = n match {
          case n: ProxyInternalNode[D] if n.isEmpty =>
            val left = sliced._2.find(_.id sameElements n.leftLabel).get.subtreeTop
            val right = sliced._2.find(_.id sameElements n.rightLabel).get.subtreeTop
            n.setChild(left)
            n.setChild(right)
          case n: InternalProverNode[D] =>
            mutateLoop(n.left)
            mutateLoop(n.right)
          case _ =>
        }

        mutateLoop(tn)
      case _: ProverLeaf[D] =>
    }

    new BatchAVLProver[D, HF](keyLength, valueLengthOpt, Some(manifest.root -> manifest.rootHeight)) {
      override val logger = serializer.logger
    }
  }

  /**
    * Serializes a manifest to bytes: root height followed by the serialized root node.
    */
  def manifestToBytes(manifest: BatchAVLProverManifest[D]): Array[Byte] = {
    Bytes.concat(
      Ints.toByteArray(manifest.rootHeight),
      nodesToBytes(manifest.root)
    )
  }

  /**
    * Deserializes a manifest from bytes.
    * Validates the root height and encoded node structure.
    */
  def manifestFromBytes(bytes: Array[Byte],
                        keyLength: Int): Try[BatchAVLProverManifest[D]] = Try {
    val oldHeight = Ints.fromByteArray(bytes.slice(0, 4))
    require(oldHeight >= 0 && oldHeight <= 256)
    val oldTop = nodesFromBytes(bytes.slice(4, bytes.length), keyLength).get
    BatchAVLProverManifest[D](oldTop, oldHeight)
  }

  /**
    * Serializes a subtree to bytes.
    */
  def subtreeToBytes(t: BatchAVLProverSubtree[D]): Array[Byte] = nodesToBytes(t.subtreeTop)

  /**
    * Deserializes a subtree from bytes.
    * Validates the encoded node structure.
    */
  def subtreeFromBytes(b: Array[Byte], kl: Int): Try[BatchAVLProverSubtree[D]] = {
    nodesFromBytes(b, kl).
      map(topNode => BatchAVLProverSubtree[D](topNode))
  }

  /**
    * Serializes a tree node and its descendants to bytes.
    */
  def nodesToBytes(rootNode: ProverNodes[D]): Array[Byte] = {
    def loop(currentNode: ProverNodes[D]): Array[Byte] = currentNode match {
      case l: ProverLeaf[D] =>
        Bytes.concat(Array(0.toByte), l.key, l.nextLeafKey, l.value)
      case n: ProxyInternalNode[D] if n.isEmpty =>
        Bytes.concat(Array(2.toByte, n.balance), n.key, n.leftLabel, n.rightLabel)
      case n: InternalProverNode[D] =>
        val leftBytes = loop(n.left)
        val rightBytes = loop(n.right)
        Bytes.concat(Array(1.toByte, n.balance), n.key, Ints.toByteArray(leftBytes.length), leftBytes, rightBytes)
    }

    loop(rootNode)
  }

  /**
    * Deserializes a tree node and its descendants from bytes.
    * Validates the encoded structure and subtree lengths.
    */
  def nodesFromBytes(bytesIn: Array[Byte], keyLength: Int): Try[ProverNodes[D]] = Try {
    require(keyLength >= 0)
    def loop(bytes: Array[Byte]): ProverNodes[D] = bytes.head match {
      case 0 =>
        val key = ADKey @@ bytes.slice(1, keyLength + 1)
        val nextLeafKey = ADKey @@ bytes.slice(keyLength + 1, 2 * keyLength + 1)
        val value = ADValue @@ bytes.slice(2 * keyLength + 1, bytes.length)
        new ProverLeaf[D](key, value, nextLeafKey)
      case 1 =>
        val balance = Balance @@ bytes.slice(1, 2).head
        val key = ADKey @@ bytes.slice(2, keyLength + 2)
        val leftLength = Ints.fromByteArray(bytes.slice(keyLength + 2, keyLength + 6))
        require(leftLength > 0 && keyLength.toLong + 6 + leftLength.toLong <= bytes.length)
        val leftBytes = bytes.slice(keyLength + 6, keyLength + 6 + leftLength)
        val rightBytes = bytes.slice(keyLength + 6 + leftLength, bytes.length)
        val left = loop(leftBytes)
        val right = loop(rightBytes)

        // check that left.key < key <= right.key
        val leftComparison = ByteArray.compare(left.key, key)
        val rightComparison = ByteArray.compare(key, right.key)
        require(leftComparison < 0 && rightComparison <= 0, s"key check fail for key ${Base16.encode(key)}")
        new InternalProverNode[D](key, left, right, balance)
      case 2 =>
        val balance = Balance @@ bytes.slice(1, 2).head
        val key = ADKey @@ bytes.slice(2, keyLength + 2)
        val leftLabel = hf.byteArrayToDigest(bytes.slice(keyLength + 2, keyLength + 2 + labelLength)).get
        val rightLabel = hf.byteArrayToDigest(bytes.slice(keyLength + 2 + labelLength, keyLength + 2 + 2 * labelLength)).get
        new ProxyInternalNode[D](key, leftLabel, rightLabel, balance)
      case _ =>
        ???
    }

    loop(bytesIn)
  }
}

