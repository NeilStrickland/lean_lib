import data.list.basic

variables {α : Type*} 

namespace list
open list 

def qualify {s : set α} (l : list α) (h : ∀ {a}, a ∈ l → s a) : list s := 
 pmap subtype.mk l @h

lemma length_qualify {s : set α} (l : list α) (h : ∀ {a}, a ∈ l → s a) :
 (qualify l @h).length = l.length := length_pmap

def unqualify {s : set α} (l : list s) : list α := l.map subtype.val 

@[simp]
lemma unqualify_nil {s : set α} : unqualify (@nil s) = nil := rfl

@[simp]
lemma unqualify_cons {s : set α} (a : s) (l : list s) : 
 unqualify (a :: l) = a.val :: (unqualify l) := rfl

lemma unqualify_eq {s : set α} {l₁ l₂ : list s} :
 l₁ = l₂ ↔ (unqualify l₁ = unqualify l₂) := 
begin
 split,
 {exact congr_arg unqualify,},
 {induction l₁ with x₁ l₁ ih generalizing l₂,
  {rw[unqualify_nil],
   rcases l₂ with _ | ⟨x₂,l₂⟩,
   {intro,refl},
   {rw[unqualify_cons],intro eu,exact false.elim (list.no_confusion eu)}
  },{
   rw[unqualify_cons],
   rcases l₂ with _ | ⟨x₂,l₂⟩,
   {intro eu,exact false.elim (list.no_confusion eu)},
   {rw[unqualify_cons],intro eu,injection eu with euh eut,congr,
    exact subtype.eq euh,exact ih eut,
   }
  }
 }
end

@[simp]
lemma length_unqualify {s : set α} (l : list s) : (unqualify l).length = l.length := 
 length_map subtype.val l

lemma mem_unqualify {s : set α} {l : list s} {a : α} : 
 a ∈ unqualify l ↔ (∃ h : s a, subtype.mk a h ∈ l) := 
begin
 rcases (@mem_map s α subtype.val a l) with ⟨h0,h1⟩,
 split,
 {intro h2,rcases h0 h2 with ⟨⟨a,a_in_s⟩,⟨a_in_l,rfl⟩⟩,exact ⟨a_in_s,a_in_l⟩ },
 {rintro ⟨a_in_s,a_in_l⟩,exact h1 ⟨⟨a,a_in_s⟩,⟨a_in_l,rfl⟩⟩}
end

lemma mem_unqualify' {s : set α} {l : list s} {a : s} : 
 a.val ∈ unqualify l ↔ a ∈ l := 
begin
 split,
 {intro h0,
  rcases (mem_unqualify.mp h0) with ⟨a_in_s,a_in_l⟩ ,
  have h1 : a = ⟨a.val,a_in_s⟩ := subtype.eq rfl,
  rw[h1],exact a_in_l,
  },
  {intro h0,exact mem_map_of_mem _ h0,}
end

@[simp]
lemma un_qualify {s : set α} (l : list α) (h : ∀ {a}, a ∈ l → s a) :
 unqualify (qualify l @h) = l := 
begin 
 dsimp[qualify],
 induction l with x l ih,
 {refl},
 {rw[unqualify,pmap,map],congr,
  exact ih (λ a a_in_l, h (mem_cons_of_mem x a_in_l)),
 }
end

def requalify {s t : set α} (l : list s) (h : ∀ {u : s}, u ∈ l → t u) : list t := 
 qualify (unqualify l) 
  (λ a a_in_l,
   begin rcases (mem_unqualify.mp a_in_l) with ⟨a_in_s,a_in_l⟩, exact h a_in_l, end )

@[simp]
lemma un_requalify {s t : set α} (l : list s) (h : ∀ {u : s}, u ∈ l → t u) : 
 unqualify (requalify l @h) = unqualify l := 
begin
 dsimp[requalify],rw[un_qualify]
end

lemma nodup_unqualify {s : set α} : ∀ {l : list s}, (unqualify l).nodup ↔ l.nodup
| [] := by { rw[unqualify_nil],simp only [nodup_nil], }
| (a :: l) := begin 
   rw[unqualify_cons,nodup_cons,nodup_cons,nodup_unqualify,@mem_unqualify' α s l a],
  end 

lemma nodup_qualify {s : set α} (l : list α) (h : ∀ {a}, a ∈ l → s a) :
 (qualify l @h).nodup ↔ l.nodup := by { rw[← nodup_unqualify,un_qualify], }

end list