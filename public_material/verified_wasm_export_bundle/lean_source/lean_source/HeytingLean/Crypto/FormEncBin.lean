import HeytingLean.Crypto.Form

namespace HeytingLean
namespace Crypto
namespace FormEncBin

open HeytingLean.Crypto

-- Tag bytes for a minimal binary encoding
def tagTop    : UInt8 := 0
def tagBot    : UInt8 := 1
def tagVar    : UInt8 := 2
def tagAnd    : UInt8 := 16
def tagOr     : UInt8 := 17
def tagImp    : UInt8 := 18

def encode3ToArray : Form 3 → Array UInt8
  | .top      => #[tagTop]
  | .bot      => #[tagBot]
  | .var i    => #[tagVar, UInt8.ofNat i.val]
  | .and a b  => #[tagAnd] ++ encode3ToArray a ++ encode3ToArray b
  | .or a b   => #[tagOr]  ++ encode3ToArray a ++ encode3ToArray b
  | .imp a b  => #[tagImp] ++ encode3ToArray a ++ encode3ToArray b

def encode3 (f : Form 3) : ByteArray :=
  ByteArray.mk (encode3ToArray f)

end FormEncBin
end Crypto
end HeytingLean
