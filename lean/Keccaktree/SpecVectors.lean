import Keccaktree.Spec
/-!
Known-answer tests for the specification, computed with an independent
implementation (`golang.org/x/crypto/sha3` `NewLegacyKeccak256`); see
`vectors/oracle.txt`.  Messages `seq n` are `n` bytes with byte `i = 7i + 3`,
chosen to cross the 136-byte rate boundary (one block, exactly one block
with padding in the next, two and three blocks).
-/
namespace Keccak.Spec.Vectors

def seq (n : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat (i * 7 + 3)

def check (m : List UInt8) (expect : String) : Bool := hex (keccak256List m) == expect

#eval check [] "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
#eval check (seq 1) "69c322e3248a5dfc29d73c5b0553b0185a35cd5bb6386747517ef7e53b15e287"
#eval check (seq 3) "7d228cdb40e661b0731cd20c876de675137701233a19b450a36e53a053407a22"
#eval check (seq 64) "0251cf13aa5b18f1cbda7cddbe85f3dc536fc93df590c2d20ca9b28af1ed2c39"
#eval check (seq 135) "00ef96af9cf4b24c7f269d922294444a197d0a33638c2e56634c57e892103a8f"
#eval check (seq 136) "742061bcad767ed4c4f5883b1dcb1aad11afdcc140dc469d953759b127b9f9ed"
#eval check (seq 137) "e3371f61e770abf254c34239c3b0099ad90594507415bc81dd0a10b9692bbf2a"
#eval check (seq 200) "66d2cdf3ab4c5bd3c75add9b60b14ac5b7789534fa2da3f348853b847359a3a0"
#eval check (seq 272) "ac141fd7b0a0ffcd2e967254d508da3ec616596493c36fa304425647d90e6de5"
#eval check (seq 300) "fa75f2293be9f9a14dcdeeff53f7b91ff6a2b1331b13886e69077ab1cf8252a9"
#eval check ("abc".toUTF8.toList) "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
#eval check (List.replicate 64 0) "ad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5"

/-- Machine-checked (not just `#eval`): the spec agrees with the oracle on the
Merkle zero-node and on a 64-byte, a 136-byte and a 300-byte message. -/
theorem vec_zero64 : check (List.replicate 64 0) "ad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5" = true := by native_decide
theorem vec_64 : check (seq 64) "0251cf13aa5b18f1cbda7cddbe85f3dc536fc93df590c2d20ca9b28af1ed2c39" = true := by native_decide
theorem vec_136 : check (seq 136) "742061bcad767ed4c4f5883b1dcb1aad11afdcc140dc469d953759b127b9f9ed" = true := by native_decide
theorem vec_300 : check (seq 300) "fa75f2293be9f9a14dcdeeff53f7b91ff6a2b1331b13886e69077ab1cf8252a9" = true := by native_decide

end Keccak.Spec.Vectors
