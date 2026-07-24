package scorex.crypto.authds.merkle.serialization

import scorex.utils.{Bytes, Ints}
import scorex.crypto.authds.merkle.BatchMerkleProof
import scorex.crypto.authds.{EmptyByteArray, Side}
import scorex.crypto.hash.{CryptographicHash, Digest, Digest32}

import scala.util.Try

/**
  * Serializer for compact Merkle multiproofs.
  */
class BatchMerkleProofSerializer[D <: Digest32, HF <: CryptographicHash[D]](implicit val hf: HF)  {

  private val digestSize = hf.DigestSize
  private val indexSize = 4
  private val sideSize = 1
  private val indicesSize = digestSize + indexSize
  private val proofsSize = digestSize + sideSize

  /**
    * Serializes a multiproof to bytes: 4-byte numIndices, 4-byte numProofs, indices, proofs.
    */
  def serialize(bmp: BatchMerkleProof[D]): Array[Byte] =
    Bytes.concat(
      Ints.toByteArray(bmp.indices.size),
      Ints.toByteArray(bmp.proofs.size),
      indicesToBytes(bmp.indices),
      proofsToBytes(bmp.proofs)
    )

  /**
    * Deserializes a multiproof from bytes.
    * Validates the header length, non-negative counts, and that the declared payload fits in the input.
    */
  def deserialize(bytes: Array[Byte]): Try[BatchMerkleProof[D]] = Try {

    require(bytes.length >= 8, "Deserialization error, empty input.")

    val numIndices = Ints.fromByteArray(bytes.slice(0, 4))
    val numProofs = Ints.fromByteArray(bytes.slice(4, 8))

    require(numIndices >= 0, "Deserialization error, invalid input.")
    require(numProofs >= 0, "Deserialization error, invalid input.")

    val expectedLength = numIndices.toLong * indicesSize + numProofs.toLong * proofsSize
    require(expectedLength <= bytes.length - 8, "Deserialization error, invalid input.")

    val (indices, proofs) = bytes.drop(8).splitAt(numIndices * indicesSize)

    require(
      indices.length == numIndices * indicesSize && proofs.length == numProofs * proofsSize,
      "Deserialization error, invalid input."
    )

    BatchMerkleProof(
      indicesFromBytes(indices),
      proofsFromBytes(proofs)
    )
  }

  private[serialization] def indicesToBytes(indices: Seq[(Int, Digest)]): Array[Byte] = {
    Bytes.concat(
      indices.map(i => (Ints.toByteArray(i._1), i._2)).flatten{case (a, b) => Bytes.concat(a, b)}.toArray
    )
  }

  private[serialization] def proofsToBytes(proofs: Seq[(Digest, Side)]): Array[Byte] = {
    Bytes.concat(
      proofs.map(p => (p._1, Array(p._2.toByte))).flatten{
        case (a, b) if a.isEmpty => Bytes.concat(Array.ofDim[Byte](32), b)
        case (a, b) => Bytes.concat(a, b)
      }.toArray
    )
  }

  private[serialization] def indicesFromBytes(bytes: Array[Byte]): Seq[(Int, Digest)] = {
    bytes.grouped(indicesSize)
      .map(b => {
        val index = Ints.fromByteArray(b.slice(0, indexSize))
        val hash = b.slice(indexSize, indicesSize).asInstanceOf[Digest]
        (index,hash)
      })
      .toSeq
  }

  private[serialization] def proofsFromBytes(bytes: Array[Byte]): Seq[(Digest, Side)] = {
    bytes.grouped(proofsSize)
      .map(b => {
        val hashBytes = b.slice(0, digestSize)
        val hash = (if (hashBytes.forall(0.toByte.equals)) EmptyByteArray else hashBytes).asInstanceOf[Digest]
        val side = b.apply(digestSize).asInstanceOf[Side]
        (hash, side)
      })
      .toSeq
  }
}