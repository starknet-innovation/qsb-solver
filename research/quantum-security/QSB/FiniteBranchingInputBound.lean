import QSB.BoundedInputEncoding
import QSB.WorldIndexedRawCacheMachine

/-!
A deterministic classical oracle machine started from one fixed state has a
finite reply tree at any fixed query budget: an H reply has exactly 32 bytes
and an R reply exactly 20 bytes. Hence some finite input length bounds all
queries in all its actual runs, even when its state and query-input types are
infinite.

The bound is existential. It can depend on the complete fixed machine and its
initial state, including oracle advice they carry. The result gives neither a
numeric byte limit from raw transaction or lock sizes nor a bound uniform over
adversarially chosen machine inputs. It does not cover entries that appear
only in an eager analytic dependency inventory, or coherent quantum queries.
-/
namespace QSB.FiniteBranchingInputBound
open ByteMachine
open CausalQueryAlgorithm (Query answer Machine run)

variable {State Out : Type*}

/-- At fixed fuel and initial state, all possible actual H/R requests have
input length below one finite bound. No finite-state assumption is needed:
the proof branches over a finite bounded-width superset of the actual
exact-width responses at each reached query. -/
theorem exists_run_input_bound (machine : Machine State Out) :
    ∀ fuel state, ∃ bound : Nat,
      ∀ functions : JointSourceChecks.Functions,
        ∀ entry ∈ (run machine functions fuel state).2,
          entry.1.input.length ≤ bound := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro state
      refine ⟨0, ?_⟩
      intro functions entry member
      simp [CausalQueryAlgorithm.run] at member
  | succ fuel ih =>
      intro state
      cases step : machine.step state with
      | inl out =>
          refine ⟨0, ?_⟩
          intro functions entry member
          simp [CausalQueryAlgorithm.run, step] at member
      | inr query =>
          let replies := BoundedInputEncoding.BoundedBytes
            (CheckedRunCacheMachine.width query)
          let tailBound : replies → Nat := fun reply =>
            Classical.choose (ih (machine.resume state reply.1))
          refine ⟨max query.input.length
            ((Finset.univ : Finset replies).sup tailBound), ?_⟩
          intro functions entry member
          let reply : replies :=
            ⟨answer functions query,
              (CheckedRunCacheMachine.answer_width functions query).le⟩
          have casesMember :
              entry = (query, answer functions query) ∨
                entry ∈ (run machine functions fuel
                  (machine.resume state (answer functions query))).2 := by
            simpa [CausalQueryAlgorithm.run, step] using member
          rcases casesMember with head | tail
          · subst entry
            exact Nat.le_max_left _ _
          · have tailLe : entry.1.input.length ≤ tailBound reply :=
              (Classical.choose_spec
                (ih (machine.resume state reply.1))) functions entry tail
            have supLe : tailBound reply ≤
                (Finset.univ : Finset replies).sup tailBound :=
              Finset.le_sup (Finset.mem_univ reply)
            exact tailLe.trans (supLe.trans (Nat.le_max_right _ _))

/-- The 1,697-request raw extractor cache machine has one finite input-byte
bound across oracle worlds when its entire fixed input is held fixed. This
statement concerns only requests actually issued by `run`; it does not claim a
bound for all eager inventory entries or for a varying adversarial input. -/
theorem fixed_raw_machine_input_bound
    (p : WorldIndexedRawCacheMachine.FixedInput) :
    ∃ bound : Nat,
      ∀ functions : JointSourceChecks.Functions,
        ∀ entry ∈
          (run (WorldIndexedRawCacheMachine.machine p) functions 1697
            ([] : CheckedRunCacheMachine.Cache)).2,
          entry.1.input.length ≤ bound :=
  exists_run_input_bound (WorldIndexedRawCacheMachine.machine p) 1697 []

end QSB.FiniteBranchingInputBound
