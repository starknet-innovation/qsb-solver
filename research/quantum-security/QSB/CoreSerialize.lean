import QSB.ByteIndex

/-!
Bitcoin Core v27.2 `CScriptNum::serialize` emits little-endian magnitude bytes
by repeatedly taking the low byte and dividing by 256, then adds a sign byte
or sign bit. `magnitudeBytes` models that loop with finite fuel. For magnitudes
below `256^fuel`, Lean proves the emitted bytes decode to the original
magnitude and extra fuel changes nothing. `ByteIndex.encodeScriptNum` now
uses the same source-shaped low-byte loop. Lean proves the two source-shaped
serializers agree for every integer, including their five-digit-domain guard.
Equality with compiled C++ remains open.
-/

namespace QSB.CoreSerialize
open QSB.ByteIndex

def magnitudeBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, magnitude =>
      if magnitude = 0 then []
      else UInt8.ofNat (magnitude % 256) ::
        magnitudeBytes fuel (magnitude / 256)

theorem magnitudeBytes_length_le (fuel magnitude : Nat) :
    (magnitudeBytes fuel magnitude).length ≤ fuel := by
  induction fuel generalizing magnitude with
  | zero => simp [magnitudeBytes]
  | succ fuel ih =>
    simp only [magnitudeBytes]
    split
    · simp
    · simp only [List.length_cons]
      have := ih (magnitude / 256)
      omega

theorem unsignedLE_magnitudeBytes (fuel magnitude : Nat)
    (bound : magnitude < 256 ^ fuel) :
    unsignedLE (magnitudeBytes fuel magnitude) = magnitude := by
  induction fuel generalizing magnitude with
  | zero =>
    have : magnitude = 0 := by simpa using bound
    simp [this, magnitudeBytes, unsignedLE]
  | succ fuel ih =>
    by_cases hz : magnitude = 0
    · simp [magnitudeBytes, hz, unsignedLE]
    · have qbound : magnitude / 256 < 256 ^ fuel := by
        rw [Nat.pow_succ] at bound
        omega
      have digit : (UInt8.ofNat (magnitude % 256)).toNat = magnitude % 256 := by
        simp
      simp [magnitudeBytes, hz, unsignedLE, digit, ih _ qbound]
      omega

/-- The source's `result.back()` read is defined after the magnitude loop
whenever the nonzero magnitude fits in the chosen fuel. -/
theorem magnitudeBytes_nonempty_of_pos (fuel magnitude : Nat)
    (bound : magnitude < 256 ^ fuel) (positive : 0 < magnitude) :
    magnitudeBytes fuel magnitude ≠ [] := by
  intro empty
  have decoded := unsignedLE_magnitudeBytes fuel magnitude bound
  simp [empty, unsignedLE] at decoded
  omega

end QSB.CoreSerialize

namespace QSB.CoreSerialize

theorem magnitudeBytes_fuel_stable (fuel magnitude : Nat)
    (bound : magnitude < 256 ^ fuel) :
    magnitudeBytes fuel.succ magnitude = magnitudeBytes fuel magnitude := by
  induction fuel generalizing magnitude with
  | zero =>
    have hz : magnitude = 0 := by simpa using bound
    simp [hz, magnitudeBytes]
  | succ fuel ih =>
    by_cases hz : magnitude = 0
    · simp [hz, magnitudeBytes]
    · have qbound : magnitude / 256 < 256 ^ fuel := by
        rw [Nat.pow_succ] at bound
        omega
      change (if magnitude = 0 then [] else UInt8.ofNat (magnitude % 256) ::
        magnitudeBytes fuel.succ (magnitude / 256)) =
        (if magnitude = 0 then [] else
          (UInt8.ofNat (magnitude % 256) ::
            magnitudeBytes fuel (magnitude / 256)))
      simp only [if_neg hz]
      rw [ih _ qbound]

end QSB.CoreSerialize

namespace QSB.CoreSerialize

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def coreSerialize (value : Int) : Option (List UInt8) :=
  let magnitude := value.natAbs
  if magnitude ≥ 256 ^ 5 then none
  else if magnitude = 0 then some []
  else
    let digits := magnitudeBytes 5 magnitude
    let high := (digits.getLast?.getD 0).toNat
    if high ≥ 128 then
      some (digits ++ [if value < 0 then 0x80 else 0x00])
    else if value < 0 then
      some (digits.dropLast ++ [UInt8.ofNat (high + 128)])
    else some digits

theorem magnitudeBytes_eq_model (fuel magnitude : Nat) :
    magnitudeBytes fuel magnitude =
      ByteIndex.magnitudeBytes fuel magnitude := by
  induction fuel generalizing magnitude with
  | zero => rfl
  | succ fuel ih =>
      simp only [magnitudeBytes, ByteIndex.magnitudeBytes]
      split
      · rfl
      · simp [ih]

/-- The byte model now uses Core's repeated-low-byte serializer directly, so
the two source-shaped encoders agree for every modeled integer. This remains
source translation, not compiled-C++ refinement. -/
theorem coreSerialize_eq_model (value : Int) :
    coreSerialize value = ByteIndex.encodeScriptNum value := by
  simp [coreSerialize, ByteIndex.encodeScriptNum, magnitudeBytes_eq_model]

theorem coreSerialize_eq_model_small_positive :
    ∀ n : Fin 1024,
      coreSerialize (Int.ofNat n.val) =
        ByteIndex.encodeScriptNum (Int.ofNat n.val) := by decide

end QSB.CoreSerialize

namespace QSB.CoreSerialize

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem coreSerialize_eq_model_small_negative :
    ∀ n : Fin 1024,
      coreSerialize (-(Int.ofNat n.val)) =
        ByteIndex.encodeScriptNum (-(Int.ofNat n.val)) := by decide

end QSB.CoreSerialize

namespace QSB.CoreSerialize

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

theorem coreSerialize_roundtrip_small_positive :
    ∀ n : Fin 1024,
      (coreSerialize (Int.ofNat n.val)).bind ByteIndex.parseScriptNum =
        some (Int.ofNat n.val) := by decide

theorem coreSerialize_roundtrip_small_negative :
    ∀ n : Fin 1024,
      (coreSerialize (-(Int.ofNat n.val))).bind ByteIndex.parseScriptNum =
        some (-(Int.ofNat n.val)) := by decide

end QSB.CoreSerialize

namespace QSB.CoreSerialize

theorem magnitudeBytes_5_length_le_4 (magnitude : Nat)
    (bound : magnitude < 256 ^ 4) :
    (magnitudeBytes 5 magnitude).length ≤ 4 := by
  rw [magnitudeBytes_fuel_stable 4 magnitude bound]
  exact magnitudeBytes_length_le 4 magnitude

end QSB.CoreSerialize

namespace QSB.CoreSerialize

/-- The finite checks above cover the entire closed signed interval. -/
theorem coreSerialize_eq_model_small (value : Int)
    (lower : -(1023 : Int) ≤ value)
    (upper : value ≤ 1023) :
    coreSerialize value = ByteIndex.encodeScriptNum value := by
  cases value with
  | ofNat n =>
    change (n : Int) ≤ 1023 at upper
    have hn : n < 1024 := by omega
    simpa using coreSerialize_eq_model_small_positive ⟨n, hn⟩
  | negSucc n =>
    have hn : n + 1 < 1024 := by omega
    simpa using coreSerialize_eq_model_small_negative ⟨n + 1, hn⟩

theorem coreSerialize_roundtrip_small (value : Int)
    (lower : -(1023 : Int) ≤ value)
    (upper : value ≤ 1023) :
    (coreSerialize value).bind ByteIndex.parseScriptNum = some value := by
  cases value with
  | ofNat n =>
    change (n : Int) ≤ 1023 at upper
    have hn : n < 1024 := by omega
    simpa using coreSerialize_roundtrip_small_positive ⟨n, hn⟩
  | negSucc n =>
    have hn : n + 1 < 1024 := by omega
    simpa using coreSerialize_roundtrip_small_negative ⟨n + 1, hn⟩

end QSB.CoreSerialize
