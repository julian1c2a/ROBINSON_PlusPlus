import ROBINSON_PlusPlus.Meta
theorem num_bridge : ∀ n : Nat,
    ROBINSON_PlusPlus.Full.numeral n = ROBINSON_PlusPlus.Meta.Godel.numeral n
  | 0 => rfl
  | n + 1 => by
      show ROBINSON_PlusPlus.Minimal.Axioms.succ (ROBINSON_PlusPlus.Full.numeral n)
         = ROBINSON_PlusPlus.Minimal.Axioms.succ (ROBINSON_PlusPlus.Meta.Godel.numeral n)
      rw [num_bridge n]
