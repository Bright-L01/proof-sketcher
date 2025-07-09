
import Foundation

-- List operations and properties

namespace List

/-- Appending nil to a list leaves it unchanged -/
theorem append_nil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp [List.append, ih]

/-- Nil is the left identity for append -/
theorem nil_append (l : List α) : [] ++ l = l := by
  rfl

/-- Length of cons is successor of tail length -/
theorem length_cons (a : α) (l : List α) : (a :: l).length = l.length + 1 := by
  simp [List.length]

/-- Append preserves length additivity -/
theorem length_append (l1 l2 : List α) : (l1 ++ l2).length = l1.length + l2.length := by
  induction l1 with
  | nil => simp [nil_append]
  | cons h t ih =>
    simp [List.append, length_cons, ih]
    rw [add_succ]

end List
