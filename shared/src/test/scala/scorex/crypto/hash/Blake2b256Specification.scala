package scorex.crypto.hash

import scorex.util.encode.Base16

class Blake2b256Specification extends HashTest {

  hashCheckString(Blake2b256,
    Map(
      "" -> "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8",
      "abc" -> "bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319"
    )
  )

  property("Blake2b256 handles large inputs (> 130 KB) and offset updates consistently across JVM and JS") {
    val large = Array.tabulate[Byte](150000)(i => (i & 0xFF).toByte)
    val expectedHex = "4b5dda69fb3a872dc124ce13f86a1dd2458fcdbf945375fd909151049cdff6e7"

    val full = Blake2b256.hash(large)
    full.length shouldBe Blake2b256.DigestSize
    Base16.encode(full) shouldBe expectedHex

    val d = Platform.createBlake2bDigest(256)
    Platform.updateDigest(d, large, 0, 75000)
    Platform.updateDigest(d, large, 75000, 75000)
    val streamed = Platform.doFinalDigest(d)
    Base16.encode(streamed) shouldBe expectedHex
  }

}
