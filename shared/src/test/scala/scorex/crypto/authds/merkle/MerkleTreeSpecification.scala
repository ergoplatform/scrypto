package scorex.crypto.authds.merkle

import org.scalatest.propspec.AnyPropSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import scorex.crypto.TestingCommons
import scorex.crypto.authds.LeafData
import scorex.crypto.hash.{Blake2b256, Digest32}

import scala.collection.mutable
import scala.util.Random

class MerkleTreeSpecification extends AnyPropSpec with ScalaCheckDrivenPropertyChecks with Matchers with TestingCommons {
  implicit val hf: Blake2b256.type = Blake2b256

  private val LeafSize = 32

  private def payloadsWithDuplicateLeaves: Seq[Seq[LeafData]] =
    Seq(
      Seq(1, 1),
      Seq(1, 2, 1),
      Seq(1, 2, 1, 3),
      Seq(1, 2, 3, 4, 1)
    ).map(_.map(value => LeafData @@ Array.fill[Byte](LeafSize)(value.toByte)))

  property("Proof generation by element") {
    forAll(smallInt) { (N: Int) =>
      whenever(N > 0) {
        val d = (0 until N).map(_ => LeafData @@ scorex.utils.Random.randomBytes(LeafSize))
        val leafs = d.map(data => Leaf(data))
        val tree = MerkleTree(d)
        leafs.foreach { l =>
          val proof = tree.proofByElement(l).get
          proof.leafData.sameElements(l.data) shouldBe true
          proof.valid(tree.rootHash) shouldBe true
        }
      }
    }
  }

  property("Proof by element hash rejects an inconsistent element index") {
    val first = LeafData @@ Array.fill[Byte](LeafSize)(1: Byte)
    val second = LeafData @@ Array.fill[Byte](LeafSize)(2: Byte)
    val firstLeaf = Leaf(first)
    val tree = MerkleTree(
      InternalNode(firstLeaf, Leaf(second)),
      Map(new mutable.WrappedArray.ofByte(firstLeaf.hash) -> 1)
    )

    tree.proofByElementHash(firstLeaf.hash) shouldBe None
  }

  property("Proof generation by index") {
    forAll(smallInt) { (N: Int) =>
      whenever(N > 0) {
        val d = (0 until N).map(_ => LeafData @@ scorex.utils.Random.randomBytes(LeafSize))
        val tree = MerkleTree(d)
        (0 until N).foreach { i =>
          tree.proofByIndex(i).get.leafData shouldEqual d(i)
          tree.proofByIndex(i).get.valid(tree.rootHash) shouldBe true
        }
        (N until N + 100).foreach { i =>
          tree.proofByIndex(i).isEmpty shouldBe true
        }
        (-(N + 100) until 0).foreach { i =>
          tree.proofByIndex(i).isEmpty shouldBe true
        }
      }
    }
  }

  property("Proof by index remains bound to the requested position with duplicate leaves") {
    val first = LeafData @@ Array.fill[Byte](LeafSize)(1: Byte)
    val second = LeafData @@ Array.fill[Byte](LeafSize)(2: Byte)
    val tree = MerkleTree(Seq(first, second, first))
    val proof = tree.proofByIndex(0).get

    proof.valid(tree.rootHash) shouldBe true
    proof.leafData.sameElements(first) shouldBe true
  }

  property("Proof generation with duplicate leaves") {
    payloadsWithDuplicateLeaves.foreach { data =>
      val tree = MerkleTree(data)

      withClue(s"leaf count ${data.length}: ") {
        tree.length shouldBe data.length
        data.indices.foreach { index =>
          val proof = tree.proofByIndex(index).get
          proof.leafData.sameElements(data(index)) shouldBe true
          proof.valid(tree.rootHash) shouldBe true
        }

        Seq(data.head, data(1)).foreach { leafData =>
          val leaf = Leaf(leafData)
          Seq(tree.proofByElement(leaf), tree.proofByElementHash(leaf.hash)).foreach { proofOpt =>
            val proof = proofOpt.get
            proof.leafData.sameElements(leafData) shouldBe true
            proof.valid(tree.rootHash) shouldBe true
          }
        }
      }
    }
  }

  property("Batch proof generation by indices") {
    val r = new Random()
    forAll(smallInt) { (N: Int) =>
      whenever(N > 0) {
        val d = (0 until N).map(_ => LeafData @@ scorex.utils.Random.randomBytes(LeafSize))
        val tree = MerkleTree(d)
        val randIndices = (0 until r.nextInt(N + 1) + 1)
          .map(_ => r.nextInt(N))
          .distinct
          .sorted
        tree.proofByIndices(randIndices).get.valid(tree.rootHash) shouldBe true
      }
    }
  }

  property("Batch proof generation by duplicated indices") {
    val d = (0 until 10).map(_ => LeafData @@ scorex.utils.Random.randomBytes(LeafSize))
    val tree = MerkleTree(d)
    tree.proofByIndices(Seq(2,2,2,3,6,6,8,9,9)).get.valid(tree.rootHash) shouldBe true
  }

  property("Batch proof generation with duplicate leaves") {
    payloadsWithDuplicateLeaves.foreach { data =>
      val tree = MerkleTree(data)
      val duplicateIndex = data.lastIndexWhere(_.sameElements(data.head))
      val requestedIndices = Seq(duplicateIndex, 0, duplicateIndex)
      val expectedIndices = requestedIndices.distinct.sorted
      val proof = tree.proofByIndices(requestedIndices).get

      withClue(s"leaf count ${data.length}: ") {
        proof.indices.map(_._1) shouldEqual expectedIndices
        proof.indices.zip(expectedIndices).foreach { case ((_, hash), index) =>
          hash.sameElements(Leaf(data(index)).hash) shouldBe true
        }
        proof.valid(tree.rootHash) shouldBe true
      }
    }
  }

  property("Batch proof generation by negative indices") {
    val d = (0 until 5).map(_ => LeafData @@ scorex.utils.Random.randomBytes(LeafSize))
    val tree = MerkleTree(d)
    tree.proofByIndices(Seq(-1,2)) shouldBe None
  }

  property("Batch proof generation by oob indices") {
    val d = (0 until 5).map(_ => LeafData @@ scorex.utils.Random.randomBytes(LeafSize))
    val tree = MerkleTree(d)
    tree.proofByIndices(Seq(2,10)) shouldBe None
  }

  property("Empty Batch proof generation should be None") {
    val d = (0 until 10).map(_ => LeafData @@ scorex.utils.Random.randomBytes(LeafSize))
    val tree = MerkleTree(d)
    tree.proofByIndices(Seq.empty[Int]) shouldBe None
  }

  property("Proof for empty node caused stack overflow") {
    val batch = BatchMerkleProof(Seq(), Seq((Digest32 @@ Array.fill[Byte](32)(0),MerkleProof.LeftSide)))
    batch.valid(Digest32 @@ Array.fill[Byte](32)(0))
  }

  property("Tree creation from 0 elements") {
    val tree = MerkleTree(Seq.empty)(hf)
    tree.rootHash shouldEqual Array.fill(hf.DigestSize)(0: Byte)
  }

  property("Tree creation from 1 element") {
    forAll { (d: Array[Byte]) =>
      whenever(d.length > 0) {
        val tree = MerkleTree(Seq(LeafData @@ d))(hf)
        tree.rootHash shouldEqual
          hf.prefixedHash(MerkleTree.InternalNodePrefix, hf.prefixedHash(MerkleTree.LeafPrefix, d))
      }
    }
  }

  property("Tree creation from 5 elements") {
    forAll { (d: Array[Byte]) =>
      whenever(d.length > 0) {
        val leafs: Seq[LeafData] = (0 until 5).map(_ => LeafData @@ d)
        val tree = MerkleTree(leafs)(hf)
        val h0x = hf.prefixedHash(MerkleTree.LeafPrefix, d)
        val h10 = hf.prefixedHash(MerkleTree.InternalNodePrefix, h0x, h0x)
        val h11 = h10
        val h12 = hf.prefixedHash(MerkleTree.InternalNodePrefix, h0x)
        val h20 = hf.prefixedHash(MerkleTree.InternalNodePrefix, h10, h11)
        val h21 = hf.prefixedHash(MerkleTree.InternalNodePrefix, h12)
        val h30 = hf.prefixedHash(MerkleTree.InternalNodePrefix, h20, h21)
        h30 shouldEqual tree.rootHash
      }
    }
  }

  property("Tree creation from 2 element") {
    forAll { (d1: Array[Byte], d2: Array[Byte]) =>
      val tree = MerkleTree(Seq(LeafData @@ d1, LeafData @@ d2))(hf)
      tree.rootHash shouldEqual
        hf.prefixedHash(MerkleTree.InternalNodePrefix,
          hf.prefixedHash(MerkleTree.LeafPrefix, d1),
          hf.prefixedHash(MerkleTree.LeafPrefix, d2))
    }
  }

  property("Tree creation from a lot of elements") {
    forAll {(d: Seq[Array[Byte]]) =>
      whenever(d.nonEmpty) {
        val tree = MerkleTree(d.map(a => LeafData @@ a))
        tree.rootHash
      }
    }
  }
}
