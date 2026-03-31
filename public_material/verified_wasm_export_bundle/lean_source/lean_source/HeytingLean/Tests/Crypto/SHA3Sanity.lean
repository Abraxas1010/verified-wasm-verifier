import HeytingLean.Util.SHA3

namespace HeytingLean.Tests.Crypto.SHA3Sanity

open HeytingLean.Util

example :
    SHA3.sha3_256Hex ByteArray.empty =
      "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a" := by
  native_decide

example :
    SHA3.sha3_512Hex ByteArray.empty =
      "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26" := by
  native_decide

example :
    SHA3.sha3_256Hex "abc".toUTF8 =
      "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532" := by
  native_decide

example :
    SHA3.shake128Hex ByteArray.empty 32 =
      "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26" := by
  native_decide

example :
    SHA3.shake256Hex ByteArray.empty 64 =
      "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be" := by
  native_decide

example :
    SHA3.shake256Hex "abc".toUTF8 64 =
      "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739d5a15bef186a5386c75744c0527e1faa9f8726e462a12a4feb06bd8801e751e4" := by
  native_decide

end HeytingLean.Tests.Crypto.SHA3Sanity
