import Keccaktree.Spec
import Keccaktree.Generic
/-! Executable check of the C and Go models against the oracle vectors (64-byte inputs). -/
namespace Keccaktree.Generic.Vectors

def seqIn (i : Nat) : BitVec 8 := BitVec.ofNat 8 (i * 7 + 3)
def digestHex (d : Vector (BitVec 8) 32) : String := Keccak.Spec.hex (d.toList.map UInt8.ofBitVec)

#eval digestHex (nodeC seqIn)
#eval digestHex (nodeC fun _ => 0)
#eval digestHex (hashC (fun i => if i < 64 then 0 else seqIn (i - 64)) 1)
#eval digestHex (nodeGo seqIn fun i => seqIn (i + 32))

theorem vec_seq64 : digestHex (nodeC seqIn) = "0251cf13aa5b18f1cbda7cddbe85f3dc536fc93df590c2d20ca9b28af1ed2c39" := by native_decide
theorem vec_zero64 : digestHex (nodeC fun _ => 0) = "ad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5" := by native_decide
theorem vec_go_seq64 : digestHex (nodeGo seqIn fun i => seqIn (i + 32)) = "0251cf13aa5b18f1cbda7cddbe85f3dc536fc93df590c2d20ca9b28af1ed2c39" := by native_decide

end Keccaktree.Generic.Vectors
