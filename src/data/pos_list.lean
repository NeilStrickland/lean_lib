inductive pos_list (α : Type) : Type 
| const : α → pos_list
| cons : α → pos_list → pos_list

namespace pos_list

variable {α : Type}

def length : pos_list α → ℕ 
| (const a) := 0
| (cons a p) := p.length.succ

def to_list : pos_list α → list α 
| (const a) := [a]
| (cons a p) := list.cons a (to_list p)

def head : pos_list α → α 
| (const a) := a
| (cons a p) := a

def foot : pos_list α → α 
| (const a) := a
| (cons a p) := p.foot

def append : pos_list α → pos_list α → pos_list α
| (const a) q := cons a q
| (cons a p) q := cons a (append p q)

lemma head_append : ∀ (p q : pos_list α),
 head (append p q) = head p
| (const a) q := rfl
| (cons a p) q := rfl

lemma foot_append : ∀ (p q : pos_list α),
 foot (append p q) = foot q
| (const a) q := rfl
| (cons a p) q := foot_append p q

lemma append_assoc : ∀ (p q r : pos_list α), 
 append (append p q) r = append p (append q r)
| (const a) q r := rfl
| (cons a p) q r := by {dsimp[append],rw[append_assoc p q r],}

def reverse : pos_list α → pos_list α 
| (const a) := const a
| (cons a p) := p.reverse.append (const a)

lemma head_reverse : ∀ (p : pos_list α), p.reverse.head = p.foot
| (const a) := rfl
| (cons a p) := by {dsimp[reverse,foot],rw[head_append,head_reverse p],}

lemma foot_reverse : ∀ (p : pos_list α), p.reverse.foot = p.head
| (const a) := rfl
| (cons a p) := by {dsimp[reverse,head],rw[foot_append],refl,}

lemma reverse_append : ∀ (p q : pos_list α),
 reverse (append p q) = append (reverse q) (reverse p) 
| (const a) q := rfl
| (cons a p) q := by {dsimp[append,reverse],rw[reverse_append p q,append_assoc],}

lemma reverse_reverse : ∀ (p : pos_list α), p.reverse.reverse = p
| (const a) := rfl
| (cons a p) := begin 
 dsimp[reverse],rw[reverse_append,reverse_reverse p],refl,
end

end pos_list

