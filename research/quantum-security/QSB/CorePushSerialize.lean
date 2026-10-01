import QSB.ScriptCodeSelection

/-!
The byte pattern built by Core v27.2's `CScript() << valtype` overload
(`src/script/script.h`, `CScript::operator<<(const std::vector<unsigned char>&)`).
In the consensus interpreter, stack elements are at most 520 bytes. The
PUSHDATA4 branch is included for source fidelity, but its four-byte length
field is only meaningful below `2^32`.
-/
namespace QSB.CorePushSerialize
open ByteMachine
set_option maxRecDepth 5000
set_option maxHeartbeats 10000000

def pushPattern (data : Bytes) : Bytes :=
  let n := data.length
  if n < 76 then
    UInt8.ofNat n :: data
  else if n ≤ 255 then
    [0x4c, UInt8.ofNat n] ++ data
  else if n ≤ 65535 then
    [0x4d, UInt8.ofNat n, UInt8.ofNat (n / 256)] ++ data
  else
    [0x4e, UInt8.ofNat n, UInt8.ofNat (n / 256),
      UInt8.ofNat (n / 65536), UInt8.ofNat (n / 16777216)] ++ data

theorem pushPattern_nonempty (data : Bytes) : pushPattern data ≠ [] := by
  dsimp [pushPattern]
  split_ifs <;> simp

/-- The existing direct-push model is exact precisely on its declared
short-signature domain, including the empty vector and length 75. -/
theorem pushPattern_direct (data : Bytes) (short : data.length < 76) :
    pushPattern data = ScriptCodeSelection.directPushPattern data := by
  simp [pushPattern, short, ScriptCodeSelection.directPushPattern]

/-- A longer signature's canonical push starts with one of the PUSHDATA
opcodes. The precise branch is determined by its byte length. -/
theorem long_head (data : Bytes) (long : 76 ≤ data.length) :
    (pushPattern data).head? = some 0x4c ∨
    (pushPattern data).head? = some 0x4d ∨
    (pushPattern data).head? = some 0x4e := by
  have notShort : ¬ data.length < 76 := by omega
  simp [pushPattern, notShort]
  split_ifs <;> simp

/-- The three consensus-reachable encoding thresholds use Core's direct,
PUSHDATA1, and PUSHDATA2 length prefixes. -/
theorem boundary_prefixes :
    (pushPattern (List.replicate 75 0x42)).take 1 = [0x4b] ∧
    (pushPattern (List.replicate 76 0x42)).take 2 = [0x4c, 0x4c] ∧
    (pushPattern (List.replicate 255 0x42)).take 2 = [0x4c, 0xff] ∧
    (pushPattern (List.replicate 256 0x42)).take 3 = [0x4d, 0x00, 0x01] ∧
    (pushPattern (List.replicate 520 0x42)).take 3 = [0x4d, 0x08, 0x02] := by
  decide

/-- A 76-byte signature is an explicit counterexample to extending the
direct-push pattern outside its short-signature domain. -/
theorem direct_pattern_wrong_at_76 :
    pushPattern (List.replicate 76 0x01) ≠
      ScriptCodeSelection.directPushPattern (List.replicate 76 0x01) := by
  decide

end QSB.CorePushSerialize
