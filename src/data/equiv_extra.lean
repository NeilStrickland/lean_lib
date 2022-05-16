import logic.equiv.basic

lemma equiv.apply {α β : Type*} (f : α ≃ β) (a : α) : 
  f a = f.to_fun a := rfl
