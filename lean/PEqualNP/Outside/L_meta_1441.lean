import Mathlib
import PEqualNP.Defs

-- Search and normalization lemmas adapt the public proof of L-meta-514.
namespace PEqualNP.Outside.L_meta_1441_aux

abbrev B := BitVec 256
abbrev Sig := B × B
def top : B := BitVec.allOnes 256
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n=k-t then
    base == top && !(v.contains g) && g != zero && g != one && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && !(v.contains g) && g != zero && g != one && r (g::(h++rest)))

def before (a b : Sig) : Bool :=
  if a.1 = b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)


def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (unaryAt k t r v (coverage (decide (0<t)) v))

def binarySlow (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  before a b &&
    (let rest := dropped [a,b] v
     let keep := [[],[a],[b],[a,b]]
     let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
     tryGate k t r v rest (v.length-2) mask (bin false a b) keep || tryGate k t r v rest (v.length-2) mask (bin true a b) keep)

def tightBinary (r : List Sig → Bool) (v : List Sig) (u : B) (a b : Sig) : Bool :=
  let ua := u &&& sep false a
  let ub := u &&& sep false b
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => !(v.contains g) && g != zero && g != one && r (g::rest)
  ((((ua &&& ~~~b.1) ||| (ub &&& ~~~a.1)) == 0) && use (bin false a b)) ||
    ((((ua &&& b.2) ||| (ub &&& a.2)) == 0) && use (bin true a b))

def binaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  if t=0 ∧ v.length-2=k then before a b && tightBinary r v c.2.1 a b
  else binarySlow k t r v c a b

private theorem need_unique (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private theorem fast_accept {k t r v c a b}
    (h : binarySlow k t r v c a b=true) : binaryAt k t r v c a b=true := by
  unfold binaryAt
  split
  · rename_i cut
    obtain ⟨rfl,hn⟩ := cut
    obtain ⟨ho,hs⟩ := Bool.and_eq_true_iff.mp h
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ho,?_⟩
    simp only [tryGate,Nat.sub_zero,hn,ite_true,Nat.lt_irrefl,decide_false,Bool.or_eq_true,Bool.and_eq_true,
      beq_iff_eq] at hs
    simp only [tightBinary,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
    rcases hs with z | z
    · exact Or.inl ⟨need_unique c a b false z.1.1.1.1,⟨⟨⟨z.1.1.1.2,z.1.1.2⟩,z.1.2⟩,z.2⟩⟩
    · exact Or.inr ⟨need_unique c a b true z.1.1.1.1,⟨⟨⟨z.1.1.1.2,z.1.1.2⟩,z.1.2⟩,z.2⟩⟩
  · exact h

private theorem fast_mono {k t v c a b} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hslow : binarySlow k t r v c a b=true → binarySlow k t s v c a b=true)
    (hr : binaryAt k t r v c a b=true) : binaryAt k t s v c a b=true := by
  by_cases hcut : t=0 ∧ v.length-2=k
  · simp only [binaryAt,if_pos hcut,tightBinary,Bool.and_eq_true,Bool.or_eq_true] at hr ⊢
    obtain ⟨order,z⟩ := hr
    refine ⟨order,?_⟩
    rcases z with ⟨p,hp,hr⟩ | ⟨p,hp,hr⟩
    · exact Or.inl ⟨p,hp,h _ hr⟩
    · exact Or.inr ⟨p,hp,h _ hr⟩
  · simpa only [binaryAt,if_neg hcut] using hslow (by simpa only [binaryAt,if_neg hcut] using hr)

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (fun a => v.any (binaryAt k t r v (coverage (decide (0<t)) v) a))

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v.contains target
  | k+1,t,v =>
    if t>k+1 ∨ v.length>k+1-t+1 then false else
    v.contains target ||
    (decide (0<t) && unaryMoves k (t-1) (search k (t-1)) v) ||
    binaryMoves k t (search k t) v

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 256
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 256
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 256)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 256) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 256 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 256)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,ha,hp.1,hp.2,hr] at *
  · simp only [tryGate,if_neg tight,Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,
      List.any_eq_true,decide_eq_true_eq,beq_iff_eq]
    exact ⟨h,hh,⟨⟨⟨⟨hl,cov⟩,ha⟩,hp.1⟩,hp.2⟩,hr⟩

private lemma ordered {a b : Sig} (h : a≠b) : before a b = true ∨ before b a = true := by
  by_cases e : a.1=b.1
  · have h2 : a.2.toNat≠b.2.toNat := fun h2 => h (Prod.ext e (BitVec.eq_of_toNat_eq h2))
    simp [before,e]; omega
  · have h1 : a.1.toNat≠b.1.toNat := fun h1 => e (BitVec.eq_of_toNat_eq h1)
    simp [before,e,Ne.symm e]; omega

private lemma unary_found {m t k : Nat} {r : List Sig → Bool} {U : Finset Sig} {a : Sig} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {r : List Sig → Bool} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (ord : before a b=true) (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have ok := gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)
  apply List.any_eq_true.mpr
  refine ⟨a,ah,List.any_eq_true.mpr ⟨b,bh,fast_accept (Bool.and_eq_true_iff.mpr ⟨ord,?_⟩)⟩⟩
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  dsimp only
  rw [hlen,hmask]
  cases d
  · exact Bool.or_eq_true_iff.mpr (Or.inl ok)
  · exact Bool.or_eq_true_iff.mpr (Or.inr ok)

private lemma search_complete {m t S} (l : Live m t S) (K : Nat) (hle : m ≤ K)
    (v : List Sig) (hv : v.Nodup) (he : v.toFinset=S) : search K t v = true := by
  have size := live_size l
  rw [←he,List.toFinset_card_of_nodup hv] at size
  induction l generalizing K v with
  | stop =>
    have ht : v.contains target = true := List.contains_iff_mem.mpr (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    cases K with
    | zero => exact ht
    | succ k =>
      rw [search,if_neg (by omega),ht]
      rfl
  | @unary m t U a ha hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr; left
      apply Bool.or_eq_true_iff.mpr; right
      apply Bool.and_eq_true_iff.mpr
      refine ⟨by simp,unary_found hv he (by omega) hf tail ?_⟩
      intro w hn eq
      have sz := live_size tail
      rw [←eq,List.toFinset_card_of_nodup hn] at sz
      exact ih k (by omega) w hn eq sz
  | @binary m t U a b d ha hb hab hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr
      right
      have cont (w : List Sig) (hn : w.Nodup) (eq : w.toFinset=insert (bin d a b) U) : search k t w = true := by
        have sz := live_size tail
        rw [←eq,List.toFinset_card_of_nodup hn] at sz
        exact ih k (by omega) w hn eq sz
      rcases ordered hab with o | o
      · exact binary_found hv he (by omega) o hab hf tail cont
      · rw [Finset.insert_comm a b] at he hf
        rw [bin_comm d a b] at hf tail cont
        exact binary_found hv he (by omega) o hab.symm hf tail cont
open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 256) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 256).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]



def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
  v.contains target || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def impossible (K t : Nat) (v : List Sig) : Prop :=
  ∀ {m S}, Live m t S → m ≤ K → v.Nodup → v.toFinset=S → False

private lemma by_search {K t v} (no : search K t v=false) : impossible K t v := by
  intro m S l le nd he
  have hit := search_complete l K le v nd he
  simp [no] at hit

private lemma reject_branch (k t : Nat) (v : List Sig) (U A : List (List Sig))
    (hu : ∀ w ∈ U, impossible k (t-1) w)
    (hb : ∀ w ∈ A, impossible k t w)
    (hc : stepTest k t v (fun w => !(U.contains w)) (fun w => !(A.contains w)) = false) :
    impossible (k+1) t v := by
  intro m S l le nd he
  have pass (n : Nat) (L : List (List Sig)) (hn : ∀ w ∈ L, impossible k n w)
      {j T} (hl : Live j n T) (hj : j≤k) (w : List Sig) (nw : w.Nodup) (ew : w.toFinset=T) :
      !(L.contains w)=true := by
    have hnm : w ∉ L := fun hw => hn w hw hl hj nw ew
    simpa [List.contains_eq_mem] using hnm
  have sz := live_size l
  rw [←he,List.toFinset_card_of_nodup nd] at sz
  unfold stepTest at hc
  rw [if_neg (by omega)] at hc
  apply Bool.noConfusion (show false=true from hc.symm.trans ?_)
  cases l with
  | stop =>
    have hit : v.contains target=true := List.contains_iff_mem.mpr (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hit)))
  | @unary j s T a ha fresh tail =>
    apply Bool.or_eq_true_iff.mpr; left
    apply Bool.or_eq_true_iff.mpr; right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp,unary_found nd he (by omega) fresh tail ?_⟩
    exact pass _ U hu tail (by omega)
  | @binary j s T a b d ha ha' hab fresh tail =>
    apply Bool.or_eq_true_iff.mpr; right
    have cont := pass _ A hb tail (by omega)
    rcases ordered hab with o | o
    · exact binary_found nd he (by omega) o hab fresh tail cont
    · rw [Finset.insert_comm a b] at he fresh
      rw [bin_comm d a b] at fresh tail cont
      exact binary_found nd he (by omega) o hab.symm fresh tail cont


lemma impossible_same {K t : Nat} {v w : List Sig}
    (e : v.toFinset = w.toFinset) (nd : v.Nodup)
    (h : impossible K t v) : impossible K t w := by
  intro m S l le _ ew
  exact h l le nd (e.trans ew)

namespace Case0

def raw0 : Sig := (0x7ffc001fff0007ffc001ffffff8003ffffffffffffc001ffffffffffffe000,0x1500a805402a01500a805402a01500a805402a01500a805402a01500a805402a)
def raw1 : Sig := (0xffffffffe0000007fffffe000ffffffc001fff0007fffffe000fff8003ffffff,0x46123091848c246123091848c246123091848c246123091848c246123091848c)
def raw2 : Sig := (0xfffffffffffffff8000000000fffffffffe0000007fffffffff0000003ffffff,0x9824c126093049824c126093049824c126093049824c126093049824c1260930)
def raw3 : Sig := (0x7ffffffffffffffffffffff00000000000000007fffffffffffffffc000000,0xe047023811c08e047023811c08e047023811c08e047023811c08e047023811c0)
def raw4 : Sig := (0x7ffffffffffffffffffffffffffffffffffffff80000000000000000000000,0x7803c01e00f007803c01e00f007803c01e00f007803c01e00f007803c01e00)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfeeaeac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 7)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 3, search 7 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 7 at hc
  exact ⟨t,by omega,search_complete ht 7 (by omega) raw raw_nd eq⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_0 : search 7 0 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_1 : search 7 1 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_2 : search 7 2 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_3 : search 7 3 raw = false := by decide +kernel

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    8 ≤ C.size := by
  by_contra! hc
  obtain ⟨t, ht, hh⟩ := circuit_search C (by omega) h he
  interval_cases t

  · rw [exclude_0] at hh; contradiction
  · rw [exclude_1] at hh; contradiction
  · rw [exclude_2] at hh; contradiction
  · rw [exclude_3] at hh; contradiction

def upperGates : List Gate := [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [10, 11]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 8 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 12⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case0

namespace Case1

def raw0 : Sig := (0xfffffff000ffffff000ffffff000ffffffffffff000fffffffffffffffffffff,0x0)
def raw1 : Sig := (0xf000ffffff000ffffff000ffffff000fff000ffffff000fff000fff000fff000,0xa12a12a12a12a12a12a12a12a12a12a12a12a12a12a12a12a12a12a12a12a12a)
def raw2 : Sig := (0xfffffffff000000000fffffffff000000fffffffff000000ffffff000000,0xca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4ca4c)
def raw3 : Sig := (0xffffffffffffffffff000000000000000fffffffffffffff000000000000,0xc70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70)
def raw4 : Sig := (0xfffffffffffffffffffffffffffffffff000000000000000000000000000,0xf80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xeeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 5)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 1, search 5 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 5 at hc
  exact ⟨t,by omega,search_complete ht 5 (by omega) raw raw_nd eq⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_0 : search 5 0 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_1 : search 5 1 raw = false := by decide +kernel

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    6 ≤ C.size := by
  by_contra! hc
  obtain ⟨t, ht, hh⟩ := circuit_search C (by omega) h he
  interval_cases t

  · rw [exclude_0] at hh; contradiction
  · rw [exclude_1] at hh; contradiction

def upperGates : List Gate := [⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 9]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 6 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 10⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case1

namespace Case2

def raw0 : Sig := (0xfffffff000ffffff000ffffff000ffffffffffff000ffffffffffff000ffffff,0x2002002002002002002002002002002002002002002002002002002002002002)
def raw1 : Sig := (0xfffffffff000ffffff000ffffff000fff000ffffff000fff000ffffff000fff,0x4124124124124124124124124124124124124124124124124124124124124124)
def raw2 : Sig := (0xf000fffffffff000000000fffffffff000000fffffffff000000fffffffff000,0x8a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48)
def raw3 : Sig := (0xffffffffffffffffff000000000000000fffffffffffffff000000000000,0xc70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70)
def raw4 : Sig := (0xfffffffffffffffffffffffffffffffff000000000000000000000000000,0xf80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xeeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 7)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 3, search 7 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 7 at hc
  exact ⟨t,by omega,search_complete ht 7 (by omega) raw raw_nd eq⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_0 : search 7 0 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_1 : search 7 1 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_2 : search 7 2 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_3 : search 7 3 raw = false := by decide +kernel

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    8 ≤ C.size := by
  by_contra! hc
  obtain ⟨t, ht, hh⟩ := circuit_search C (by omega) h he
  interval_cases t

  · rw [exclude_0] at hh; contradiction
  · rw [exclude_1] at hh; contradiction
  · rw [exclude_2] at hh; contradiction
  · rw [exclude_3] at hh; contradiction

def upperGates : List Gate := [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [9, 11]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 8 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 12⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case2

namespace Case3

def raw0 : Sig := (0xfffffff000ffffff000ffffff000ffffffffffff000ffffff000fff000ffffff,0x2022022022022022022022022022022022022022022022022022022022022022)
def raw1 : Sig := (0xfffffffff000ffffff000ffffff000fff000ffffff000ffffffffffff000fff,0x4104104104104104104104104104104104104104104104104104104104104104)
def raw2 : Sig := (0xf000fffffffff000000000fffffffff000000fffffffff000000fffffffff000,0x8a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48a48)
def raw3 : Sig := (0xffffffffffffffffff000000000000000fffffffffffffff000000000000,0xc70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70c70)
def raw4 : Sig := (0xfffffffffffffffffffffffffffffffff000000000000000000000000000,0xf80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xeeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 5)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 1, search 5 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 5 at hc
  exact ⟨t,by omega,search_complete ht 5 (by omega) raw raw_nd eq⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_0 : search 5 0 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_1 : search 5 1 raw = false := by decide +kernel

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    6 ≤ C.size := by
  by_contra! hc
  obtain ⟨t, ht, hh⟩ := circuit_search C (by omega) h he
  interval_cases t

  · rw [exclude_0] at hh; contradiction
  · rw [exclude_1] at hh; contradiction

def upperGates : List Gate := [⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [8, 9]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 6 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 10⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case3

namespace Case4

def raw0 : Sig := (0xffffff000ffffff000ffffff000ffffffffffff000ffffff000ffffff000fff,0xa00a00a00a00a00a00a00a00a00a00a00a00a00a00a00a00a00a00a00a00a00a)
def raw1 : Sig := (0xf000ffffff000ffffff000ffffff000fff000ffffff000ffffff000ffffff000,0xc10c10c10c10c10c10c10c10c10c10c10c10c10c10c10c10c10c10c10c10c10c)
def raw2 : Sig := (0xfffffffffffff000000000fffffffff000000fffffffff000000000fffffffff,0xa50a50a50a50a50a50a50a50a50a50a50a50a50a50a50a50a50a50a50a50a50)
def raw3 : Sig := (0xffffffffffffffffff000000000000000ffffffffffffffffff000000000,0xc60c60c60c60c60c60c60c60c60c60c60c60c60c60c60c60c60c60c60c60c60)
def raw4 : Sig := (0xfffffffffffffffffffffffffffffffff000000000000000000000000000,0xf80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xeeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 4)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 0, search 4 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 4 at hc
  exact ⟨t,by omega,search_complete ht 4 (by omega) raw raw_nd eq⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_0 : search 4 0 raw = false := by decide +kernel

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    5 ≤ C.size := by
  by_contra! hc
  obtain ⟨t, ht, hh⟩ := circuit_search C (by omega) h he
  interval_cases t

  · rw [exclude_0] at hh; contradiction

def upperGates : List Gate := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [7, 8]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 5 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 9⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case4

namespace Case5

def raw0 : Sig := (0xfffffff000fff000fff000ffffff000fffffffff000ffffffffffff000ffffff,0x2102102102102102102102102102102102102102102102102102102102102102)
def raw1 : Sig := (0xfffffffff000000ffffff000ffffff000fffffffff000fff000ffffff000fff,0x4224224224224224224224224224224224224224224224224224224224224224)
def raw2 : Sig := (0xf000ffffffffffff000000000fffffffff000fffffffff000000fffffffff000,0x8448448448448448448448448448448448448448448448448448448448448448)
def raw3 : Sig := (0xfffffffffffffffffffff000000000000fffffffffffffff000000000000,0x870870870870870870870870870870870870870870870870870870870870870)
def raw4 : Sig := (0xfffffffffffffffffffffffffffffffff000000000000000000000000000,0xf80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfee8eae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 7)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 3, search 7 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 7 at hc
  exact ⟨t,by omega,search_complete ht 7 (by omega) raw raw_nd eq⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_0 : search 7 0 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_1 : search 7 1 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_2 : search 7 2 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_3 : search 7 3 raw = false := by decide +kernel

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    8 ≤ C.size := by
  by_contra! hc
  obtain ⟨t, ht, hh⟩ := circuit_search C (by omega) h he
  interval_cases t

  · rw [exclude_0] at hh; contradiction
  · rw [exclude_1] at hh; contradiction
  · rw [exclude_2] at hh; contradiction
  · rw [exclude_3] at hh; contradiction

def upperGates : List Gate := [⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [10, 11]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 8 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 12⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case5

namespace Case6

def raw0 : Sig := (0xffffff000fff000fff000ffffff000fffffffff000ffffff000ffffff000fff,0xa10a10a10a10a10a10a10a10a10a10a10a10a10a10a10a10a10a10a10a10a10a)
def raw1 : Sig := (0xf000ffffff000000ffffff000ffffff000fffffffff000ffffff000ffffff000,0xc20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c)
def raw2 : Sig := (0xffffffffffffffff000000000fffffffff000fffffffff000000000fffffffff,0x450450450450450450450450450450450450450450450450450450450450450)
def raw3 : Sig := (0xfffffffffffffffffffff000000000000ffffffffffffffffff000000000,0x860860860860860860860860860860860860860860860860860860860860860)
def raw4 : Sig := (0xfffffffffffffffffffffffffffffffff000000000000000000000000000,0xf80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80f80)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfee8eee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 7)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 3, search 7 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 7 at hc
  exact ⟨t,by omega,search_complete ht 7 (by omega) raw raw_nd eq⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_0 : search 7 0 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_1 : search 7 1 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_2 : search 7 2 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_3 : search 7 3 raw = false := by decide +kernel

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    8 ≤ C.size := by
  by_contra! hc
  obtain ⟨t, ht, hh⟩ := circuit_search C (by omega) h he
  interval_cases t

  · rw [exclude_0] at hh; contradiction
  · rw [exclude_1] at hh; contradiction
  · rw [exclude_2] at hh; contradiction
  · rw [exclude_3] at hh; contradiction

def upperGates : List Gate := [⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [10, 11]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 8 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 12⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case6

namespace Case7

def raw0 : Sig := (0xfffffff000fff000fff000ffffff000ffffffffffff000ffffffffffffffffff,0x2002002002002002002002002002002002002002002002002002002002002002)
def raw1 : Sig := (0xfffffffff000000ffffff000ffffff000fff000ffffff000fff000fff000fff,0x4254254254254254254254254254254254254254254254254254254254254254)
def raw2 : Sig := (0xf000ffffffffffff000000000fffffffff000000fffffffff000000ffffff000,0x8498498498498498498498498498498498498498498498498498498498498498)
def raw3 : Sig := (0xfffffffffffffffffffff000000000000000fffffffffffffff000000000,0x8e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e0)
def raw4 : Sig := (0xffffffffffffffffffffffffffffffffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 8)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 4, search 8 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 8 at hc
  exact ⟨t,by omega,search_complete ht 8 (by omega) raw raw_nd eq⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_1 : search 8 1 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_2 : search 8 2 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_3 : search 8 3 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_4 : search 8 4 raw = false := by decide +kernel

def b0_w0 : Sig := bin false raw3 raw4
def b0_w1 : Sig := bin true raw3 raw4
def b0_w2 : Sig := bin false raw3 raw1
def b0_w3 : Sig := bin true raw3 raw1
def b0_w4 : Sig := bin false raw3 raw2
def b0_w5 : Sig := bin true raw3 raw2
def b0_w6 : Sig := bin false raw3 raw0
def b0_w7 : Sig := bin true raw3 raw0
def b0_w8 : Sig := bin false raw4 raw1
def b0_w9 : Sig := bin true raw4 raw1
def b0_w10 : Sig := bin false raw4 raw2
def b0_w11 : Sig := bin true raw4 raw2
def b0_w12 : Sig := bin false raw4 raw0
def b0_w13 : Sig := bin true raw4 raw0
def b0_w14 : Sig := bin false raw1 raw2
def b0_w15 : Sig := bin true raw1 raw2
def b0_w16 : Sig := bin false raw1 raw0
def b0_w17 : Sig := bin true raw1 raw0
def b0_w18 : Sig := bin false raw2 raw0
def b0_w19 : Sig := bin true raw2 raw0
def b0_w20 : Sig := bin false b0_w0 raw1
def b0_w21 : Sig := bin true b0_w0 raw1
def b0_w22 : Sig := bin false b0_w0 raw2
def b0_w23 : Sig := bin true b0_w0 raw2
def b0_w24 : Sig := bin false b0_w0 raw0
def b0_w25 : Sig := bin true b0_w0 raw0
def b0_w26 : Sig := bin false b0_w1 raw1
def b0_w27 : Sig := bin true b0_w1 raw1
def b0_w28 : Sig := bin false b0_w1 raw2
def b0_w29 : Sig := bin true b0_w1 raw2
def b0_w30 : Sig := bin false b0_w1 raw0
def b0_w31 : Sig := bin true b0_w1 raw0
def b0_w32 : Sig := bin true b0_w2 raw4
def b0_w33 : Sig := bin false b0_w2 raw2
def b0_w34 : Sig := bin true b0_w2 raw2
def b0_w35 : Sig := bin false b0_w2 raw0
def b0_w36 : Sig := bin true b0_w2 raw0
def b0_w37 : Sig := bin false raw4 b0_w3
def b0_w38 : Sig := bin false b0_w3 raw2
def b0_w39 : Sig := bin true b0_w3 raw2
def b0_w40 : Sig := bin false b0_w3 raw0
def b0_w41 : Sig := bin true b0_w3 raw0
def b0_w42 : Sig := bin true b0_w4 raw4
def b0_w43 : Sig := bin true b0_w4 raw1
def b0_w44 : Sig := bin false b0_w4 raw0
def b0_w45 : Sig := bin true b0_w4 raw0
def b0_w46 : Sig := bin false raw4 b0_w5
def b0_w47 : Sig := bin false raw1 b0_w5
def b0_w48 : Sig := bin false b0_w5 raw0
def b0_w49 : Sig := bin true b0_w5 raw0
def b0_w50 : Sig := bin true b0_w6 raw4
def b0_w51 : Sig := bin true b0_w6 raw1
def b0_w52 : Sig := bin true b0_w6 raw2
def b0_w53 : Sig := bin false raw4 b0_w7
def b0_w54 : Sig := bin false raw1 b0_w7
def b0_w55 : Sig := bin false raw2 b0_w7
def b0_w56 : Sig := bin true b0_w8 raw3
def b0_w57 : Sig := bin false b0_w8 raw2
def b0_w58 : Sig := bin true b0_w8 raw2
def b0_w59 : Sig := bin false b0_w8 raw0
def b0_w60 : Sig := bin true b0_w8 raw0
def b0_w61 : Sig := bin false raw3 b0_w9
def b0_w62 : Sig := bin false b0_w9 raw2
def b0_w63 : Sig := bin true b0_w9 raw2
def b0_w64 : Sig := bin false b0_w9 raw0
def b0_w65 : Sig := bin true b0_w9 raw0
def b0_w66 : Sig := bin true b0_w10 raw3
def b0_w67 : Sig := bin true b0_w10 raw1
def b0_w68 : Sig := bin false b0_w10 raw0
def b0_w69 : Sig := bin true b0_w10 raw0
def b0_w70 : Sig := bin false raw3 b0_w11
def b0_w71 : Sig := bin false raw1 b0_w11
def b0_w72 : Sig := bin false b0_w11 raw0
def b0_w73 : Sig := bin true b0_w11 raw0
def b0_w74 : Sig := bin true b0_w12 raw3
def b0_w75 : Sig := bin true b0_w12 raw1
def b0_w76 : Sig := bin true b0_w12 raw2
def b0_w77 : Sig := bin false raw3 b0_w13
def b0_w78 : Sig := bin false raw1 b0_w13
def b0_w79 : Sig := bin false raw2 b0_w13
def b0_w80 : Sig := bin true b0_w14 raw3
def b0_w81 : Sig := bin true b0_w14 raw4
def b0_w82 : Sig := bin false b0_w14 raw0
def b0_w83 : Sig := bin true b0_w14 raw0
def b0_w84 : Sig := bin false raw3 b0_w15
def b0_w85 : Sig := bin false raw4 b0_w15
def b0_w86 : Sig := bin false raw0 b0_w15
def b0_w87 : Sig := bin true raw0 b0_w15
def b0_w88 : Sig := bin true raw3 b0_w16
def b0_w89 : Sig := bin true raw4 b0_w16
def b0_w90 : Sig := bin true b0_w16 raw2
def b0_w91 : Sig := bin false raw3 b0_w17
def b0_w92 : Sig := bin false raw4 b0_w17
def b0_w93 : Sig := bin false raw2 b0_w17
def b0_w94 : Sig := bin true raw3 b0_w18
def b0_w95 : Sig := bin true raw4 b0_w18
def b0_w96 : Sig := bin true raw1 b0_w18
def b0_w97 : Sig := bin false raw3 b0_w19
def b0_w98 : Sig := bin false raw4 b0_w19
def b0_w99 : Sig := bin false raw1 b0_w19

def b0_s2 : List Sig := [b0_w20,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead2 : impossible 6 0 b0_s2 := by
  apply by_search
  decide +kernel

def b0_s3 : List Sig := [b0_w20,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead3 : impossible 6 0 b0_s3 := by
  apply by_search
  decide +kernel

def b0_s4 : List Sig := [raw3,raw4,raw1,b0_w21,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead4 : impossible 6 0 b0_s4 := by
  apply by_search
  decide +kernel

def b0_s5 : List Sig := [b0_w0,raw3,raw4,raw1,b0_w21,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead5 : impossible 6 0 b0_s5 := by
  apply by_search
  decide +kernel

def b0_s6 : List Sig := [b0_w22,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead6 : impossible 6 0 b0_s6 := by
  apply by_search
  decide +kernel

def b0_s7 : List Sig := [b0_w22,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead7 : impossible 6 0 b0_s7 := by
  apply by_search
  decide +kernel

def b0_s8 : List Sig := [raw3,raw4,raw1,raw2,b0_w23,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead8 : impossible 6 0 b0_s8 := by
  apply by_search
  decide +kernel

def b0_s9 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,b0_w23,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead9 : impossible 6 0 b0_s9 := by
  apply by_search
  decide +kernel

def b0_s10 : List Sig := [b0_w24,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead10 : impossible 6 0 b0_s10 := by
  apply by_search
  decide +kernel

def b0_s11 : List Sig := [b0_w24,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead11 : impossible 6 0 b0_s11 := by
  apply by_search
  decide +kernel

def b0_s12 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w25]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead12 : impossible 6 0 b0_s12 := by
  apply by_search
  decide +kernel

def b0_s13 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w25]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead13 : impossible 6 0 b0_s13 := by
  apply by_search
  decide +kernel

def b0_s14 : List Sig := [b0_w0,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead14 : impossible 6 0 b0_s14 := by
  apply by_search
  decide +kernel

def b0_s15 : List Sig := [b0_w0,raw3,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead15 : impossible 6 0 b0_s15 := by
  apply by_search
  decide +kernel

def b0_s16 : List Sig := [b0_w0,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead16 : impossible 6 0 b0_s16 := by
  apply by_search
  decide +kernel

def b0_s17 : List Sig := [b0_w0,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead17 : impossible 6 0 b0_s17 := by
  apply by_search
  decide +kernel

def b0_s18 : List Sig := [b0_w2,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead18 : impossible 6 0 b0_s18 := by
  apply by_search
  decide +kernel

def b0_s19 : List Sig := [b0_w0,raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead19 : impossible 6 0 b0_s19 := by
  apply by_search
  decide +kernel

def b0_s20 : List Sig := [b0_w4,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead20 : impossible 6 0 b0_s20 := by
  apply by_search
  decide +kernel

def b0_s21 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead21 : impossible 6 0 b0_s21 := by
  apply by_search
  decide +kernel

def b0_s22 : List Sig := [b0_w6,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead22 : impossible 6 0 b0_s22 := by
  apply by_search
  decide +kernel

def b0_s23 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead23 : impossible 6 0 b0_s23 := by
  apply by_search
  decide +kernel

def b0_s24 : List Sig := [b0_w8,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead24 : impossible 6 0 b0_s24 := by
  apply by_search
  decide +kernel

def b0_s25 : List Sig := [b0_w0,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead25 : impossible 6 0 b0_s25 := by
  apply by_search
  decide +kernel

def b0_s26 : List Sig := [b0_w10,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead26 : impossible 6 0 b0_s26 := by
  apply by_search
  decide +kernel

def b0_s27 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead27 : impossible 6 0 b0_s27 := by
  apply by_search
  decide +kernel

def b0_s28 : List Sig := [b0_w12,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead28 : impossible 6 0 b0_s28 := by
  apply by_search
  decide +kernel

def b0_s29 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead29 : impossible 6 0 b0_s29 := by
  apply by_search
  decide +kernel

def b0_s30 : List Sig := [b0_w14,b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead30 : impossible 6 0 b0_s30 := by
  apply by_search
  decide +kernel

def b0_s31 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead31 : impossible 6 0 b0_s31 := by
  apply by_search
  decide +kernel

def b0_s32 : List Sig := [b0_w0,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead32 : impossible 6 0 b0_s32 := by
  apply by_search
  decide +kernel

def b0_s33 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead33 : impossible 6 0 b0_s33 := by
  apply by_search
  decide +kernel

def b0_s34 : List Sig := [b0_w0,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead34 : impossible 6 0 b0_s34 := by
  apply by_search
  decide +kernel

def b0_s35 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead35 : impossible 6 0 b0_s35 := by
  apply by_search
  decide +kernel

def b0_s1 : List Sig := [b0_w0,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead1 : impossible 7 0 b0_s1 := by
  apply reject_branch 6 0 b0_s1 [] [[b0_w20,raw1,raw3,raw4,raw2,raw0],[b0_w20,b0_w0,raw1,raw3,raw4,raw2,raw0],[b0_w21,raw1,raw3,raw4,raw2,raw0],[b0_w21,b0_w0,raw1,raw3,raw4,raw2,raw0],[b0_w22,raw2,raw3,raw4,raw1,raw0],[b0_w22,b0_w0,raw2,raw3,raw4,raw1,raw0],[b0_w23,raw2,raw3,raw4,raw1,raw0],[b0_w23,b0_w0,raw2,raw3,raw4,raw1,raw0],[b0_w24,raw0,raw3,raw4,raw1,raw2],[b0_w24,b0_w0,raw0,raw3,raw4,raw1,raw2],[b0_w25,raw0,raw3,raw4,raw1,raw2],[b0_w25,b0_w0,raw0,raw3,raw4,raw1,raw2],[b0_w1,b0_w0,raw1,raw2,raw0],[b0_w1,raw3,b0_w0,raw1,raw2,raw0],[b0_w1,raw4,b0_w0,raw1,raw2,raw0],[b0_w1,raw3,raw4,b0_w0,raw1,raw2,raw0],[b0_w2,raw3,raw1,b0_w0,raw4,raw2,raw0],[b0_w3,raw3,raw1,b0_w0,raw4,raw2,raw0],[b0_w4,raw3,raw2,b0_w0,raw4,raw1,raw0],[b0_w5,raw3,raw2,b0_w0,raw4,raw1,raw0],[b0_w6,raw3,raw0,b0_w0,raw4,raw1,raw2],[b0_w7,raw3,raw0,b0_w0,raw4,raw1,raw2],[b0_w8,raw4,raw1,b0_w0,raw3,raw2,raw0],[b0_w9,raw4,raw1,b0_w0,raw3,raw2,raw0],[b0_w10,raw4,raw2,b0_w0,raw3,raw1,raw0],[b0_w11,raw4,raw2,b0_w0,raw3,raw1,raw0],[b0_w12,raw4,raw0,b0_w0,raw3,raw1,raw2],[b0_w13,raw4,raw0,b0_w0,raw3,raw1,raw2],[b0_w14,raw1,raw2,b0_w0,raw3,raw4,raw0],[b0_w15,raw1,raw2,b0_w0,raw3,raw4,raw0],[b0_w16,raw1,raw0,b0_w0,raw3,raw4,raw2],[b0_w17,raw1,raw0,b0_w0,raw3,raw4,raw2],[b0_w18,raw2,raw0,b0_w0,raw3,raw4,raw1],[b0_w19,raw2,raw0,b0_w0,raw3,raw4,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead2
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead3
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead4
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead5
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead6
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead7
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead8
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead9
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead10
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead11
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead12
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead13
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead14
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead15
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead16
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead17
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead18
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead19
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead20
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead21
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead22
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead23
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead24
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead25
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead26
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead27
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead28
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead29
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead30
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead31
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead32
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead33
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead34
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead35
  · decide +kernel

def b0_s37 : List Sig := [b0_w2,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead37 : impossible 6 0 b0_s37 := by
  apply by_search
  decide +kernel

def b0_s38 : List Sig := [raw3,raw4,b0_w1,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead38 : impossible 6 0 b0_s38 := by
  apply by_search
  decide +kernel

def b0_s39 : List Sig := [b0_w4,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead39 : impossible 6 0 b0_s39 := by
  apply by_search
  decide +kernel

def b0_s40 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead40 : impossible 6 0 b0_s40 := by
  apply by_search
  decide +kernel

def b0_s41 : List Sig := [b0_w6,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead41 : impossible 6 0 b0_s41 := by
  apply by_search
  decide +kernel

def b0_s42 : List Sig := [raw4,b0_w1,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead42 : impossible 6 0 b0_s42 := by
  apply by_search
  decide +kernel

def b0_s43 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead43 : impossible 6 0 b0_s43 := by
  apply by_search
  decide +kernel

def b0_s44 : List Sig := [b0_w8,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead44 : impossible 6 0 b0_s44 := by
  apply by_search
  decide +kernel

def b0_s45 : List Sig := [raw3,raw4,b0_w1,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead45 : impossible 6 0 b0_s45 := by
  apply by_search
  decide +kernel

def b0_s46 : List Sig := [b0_w10,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead46 : impossible 6 0 b0_s46 := by
  apply by_search
  decide +kernel

def b0_s47 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead47 : impossible 6 0 b0_s47 := by
  apply by_search
  decide +kernel

def b0_s48 : List Sig := [b0_w12,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead48 : impossible 6 0 b0_s48 := by
  apply by_search
  decide +kernel

def b0_s49 : List Sig := [raw3,b0_w1,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead49 : impossible 6 0 b0_s49 := by
  apply by_search
  decide +kernel

def b0_s50 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead50 : impossible 6 0 b0_s50 := by
  apply by_search
  decide +kernel

def b0_s51 : List Sig := [b0_w26,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead51 : impossible 6 0 b0_s51 := by
  apply by_search
  decide +kernel

def b0_s52 : List Sig := [b0_w26,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead52 : impossible 6 0 b0_s52 := by
  apply by_search
  decide +kernel

def b0_s53 : List Sig := [raw3,raw4,raw1,b0_w27,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead53 : impossible 6 0 b0_s53 := by
  apply by_search
  decide +kernel

def b0_s54 : List Sig := [raw3,raw4,b0_w1,raw1,b0_w27,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead54 : impossible 6 0 b0_s54 := by
  apply by_search
  decide +kernel

def b0_s55 : List Sig := [b0_w28,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead55 : impossible 6 0 b0_s55 := by
  apply by_search
  decide +kernel

def b0_s56 : List Sig := [b0_w28,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead56 : impossible 6 0 b0_s56 := by
  apply by_search
  decide +kernel

def b0_s57 : List Sig := [raw3,raw4,raw1,raw2,b0_w29,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead57 : impossible 6 0 b0_s57 := by
  apply by_search
  decide +kernel

def b0_s58 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,b0_w29,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead58 : impossible 6 0 b0_s58 := by
  apply by_search
  decide +kernel

def b0_s59 : List Sig := [b0_w30,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead59 : impossible 6 0 b0_s59 := by
  apply by_search
  decide +kernel

def b0_s60 : List Sig := [b0_w30,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead60 : impossible 6 0 b0_s60 := by
  apply by_search
  decide +kernel

def b0_s61 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w31]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead61 : impossible 6 0 b0_s61 := by
  apply by_search
  decide +kernel

def b0_s62 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,raw0,b0_w31]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead62 : impossible 6 0 b0_s62 := by
  apply by_search
  decide +kernel

def b0_s63 : List Sig := [b0_w14,raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead63 : impossible 6 0 b0_s63 := by
  apply by_search
  decide +kernel

def b0_s64 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead64 : impossible 6 0 b0_s64 := by
  apply by_search
  decide +kernel

def b0_s65 : List Sig := [raw3,raw4,b0_w1,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead65 : impossible 6 0 b0_s65 := by
  apply by_search
  decide +kernel

def b0_s66 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead66 : impossible 6 0 b0_s66 := by
  apply by_search
  decide +kernel

def b0_s67 : List Sig := [raw3,raw4,b0_w1,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead67 : impossible 6 0 b0_s67 := by
  apply by_search
  decide +kernel

def b0_s68 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead68 : impossible 6 0 b0_s68 := by
  apply by_search
  decide +kernel

def b0_s36 : List Sig := [raw3,raw4,b0_w1,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead36 : impossible 7 0 b0_s36 := by
  apply reject_branch 6 0 b0_s36 [] [[b0_w0,b0_w1,raw1,raw2,raw0],[b0_w0,raw3,b0_w1,raw1,raw2,raw0],[b0_w0,raw4,b0_w1,raw1,raw2,raw0],[b0_w0,raw3,raw4,b0_w1,raw1,raw2,raw0],[b0_w2,raw3,raw1,raw4,b0_w1,raw2,raw0],[b0_w3,raw3,raw1,raw4,b0_w1,raw2,raw0],[b0_w4,raw3,raw2,raw4,b0_w1,raw1,raw0],[b0_w5,raw3,raw2,raw4,b0_w1,raw1,raw0],[b0_w6,raw3,raw0,raw4,b0_w1,raw1,raw2],[b0_w7,raw0,raw4,b0_w1,raw1,raw2],[b0_w7,raw3,raw0,raw4,b0_w1,raw1,raw2],[b0_w8,raw4,raw1,raw3,b0_w1,raw2,raw0],[b0_w9,raw4,raw1,raw3,b0_w1,raw2,raw0],[b0_w10,raw4,raw2,raw3,b0_w1,raw1,raw0],[b0_w11,raw4,raw2,raw3,b0_w1,raw1,raw0],[b0_w12,raw4,raw0,raw3,b0_w1,raw1,raw2],[b0_w13,raw0,raw3,b0_w1,raw1,raw2],[b0_w13,raw4,raw0,raw3,b0_w1,raw1,raw2],[b0_w26,raw1,raw3,raw4,raw2,raw0],[b0_w26,b0_w1,raw1,raw3,raw4,raw2,raw0],[b0_w27,raw1,raw3,raw4,raw2,raw0],[b0_w27,b0_w1,raw1,raw3,raw4,raw2,raw0],[b0_w28,raw2,raw3,raw4,raw1,raw0],[b0_w28,b0_w1,raw2,raw3,raw4,raw1,raw0],[b0_w29,raw2,raw3,raw4,raw1,raw0],[b0_w29,b0_w1,raw2,raw3,raw4,raw1,raw0],[b0_w30,raw0,raw3,raw4,raw1,raw2],[b0_w30,b0_w1,raw0,raw3,raw4,raw1,raw2],[b0_w31,raw0,raw3,raw4,raw1,raw2],[b0_w31,b0_w1,raw0,raw3,raw4,raw1,raw2],[b0_w14,raw1,raw2,raw3,raw4,b0_w1,raw0],[b0_w15,raw1,raw2,raw3,raw4,b0_w1,raw0],[b0_w16,raw1,raw0,raw3,raw4,b0_w1,raw2],[b0_w17,raw1,raw0,raw3,raw4,b0_w1,raw2],[b0_w18,raw2,raw0,raw3,raw4,b0_w1,raw1],[b0_w19,raw2,raw0,raw3,raw4,b0_w1,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead14
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead15
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead16
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead17
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead37
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead38
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead39
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead40
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead41
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead42
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead43
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead44
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead45
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead46
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead47
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead48
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead49
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead50
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead51
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead52
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead53
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead54
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead55
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead56
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead57
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead58
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead59
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead60
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead61
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead62
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead63
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead64
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead65
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead66
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead67
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead68
  · decide +kernel

def b0_s70 : List Sig := [b0_w20,b0_w2,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead70 : impossible 6 0 b0_s70 := by
  apply by_search
  decide +kernel

def b0_s71 : List Sig := [raw3,raw4,b0_w32,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead71 : impossible 6 0 b0_s71 := by
  apply by_search
  decide +kernel

def b0_s72 : List Sig := [b0_w2,raw3,raw4,b0_w32,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead72 : impossible 6 0 b0_s72 := by
  apply by_search
  decide +kernel

def b0_s73 : List Sig := [b0_w33,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead73 : impossible 6 0 b0_s73 := by
  apply by_search
  decide +kernel

def b0_s74 : List Sig := [b0_w33,b0_w2,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead74 : impossible 6 0 b0_s74 := by
  apply by_search
  decide +kernel

def b0_s75 : List Sig := [raw3,raw4,raw1,raw2,b0_w34,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead75 : impossible 6 0 b0_s75 := by
  apply by_search
  decide +kernel

def b0_s76 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,b0_w34,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead76 : impossible 6 0 b0_s76 := by
  apply by_search
  decide +kernel

def b0_s77 : List Sig := [b0_w35,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead77 : impossible 6 0 b0_s77 := by
  apply by_search
  decide +kernel

def b0_s78 : List Sig := [b0_w35,b0_w2,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead78 : impossible 6 0 b0_s78 := by
  apply by_search
  decide +kernel

def b0_s79 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w36]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead79 : impossible 6 0 b0_s79 := by
  apply by_search
  decide +kernel

def b0_s80 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,raw0,b0_w36]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead80 : impossible 6 0 b0_s80 := by
  apply by_search
  decide +kernel

def b0_s81 : List Sig := [b0_w2,raw4,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead81 : impossible 6 0 b0_s81 := by
  apply by_search
  decide +kernel

def b0_s82 : List Sig := [b0_w2,raw3,raw4,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead82 : impossible 6 0 b0_s82 := by
  apply by_search
  decide +kernel

def b0_s83 : List Sig := [b0_w2,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead83 : impossible 6 0 b0_s83 := by
  apply by_search
  decide +kernel

def b0_s84 : List Sig := [b0_w2,raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead84 : impossible 6 0 b0_s84 := by
  apply by_search
  decide +kernel

def b0_s85 : List Sig := [b0_w2,b0_w4,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead85 : impossible 6 0 b0_s85 := by
  apply by_search
  decide +kernel

def b0_s86 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead86 : impossible 6 0 b0_s86 := by
  apply by_search
  decide +kernel

def b0_s87 : List Sig := [b0_w6,b0_w2,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead87 : impossible 6 0 b0_s87 := by
  apply by_search
  decide +kernel

def b0_s88 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead88 : impossible 6 0 b0_s88 := by
  apply by_search
  decide +kernel

def b0_s89 : List Sig := [b0_w2,b0_w8,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead89 : impossible 6 0 b0_s89 := by
  apply by_search
  decide +kernel

def b0_s90 : List Sig := [b0_w2,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead90 : impossible 6 0 b0_s90 := by
  apply by_search
  decide +kernel

def b0_s91 : List Sig := [b0_w2,b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead91 : impossible 6 0 b0_s91 := by
  apply by_search
  decide +kernel

def b0_s92 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead92 : impossible 6 0 b0_s92 := by
  apply by_search
  decide +kernel

def b0_s93 : List Sig := [b0_w12,b0_w2,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead93 : impossible 6 0 b0_s93 := by
  apply by_search
  decide +kernel

def b0_s94 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead94 : impossible 6 0 b0_s94 := by
  apply by_search
  decide +kernel

def b0_s95 : List Sig := [b0_w14,b0_w2,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead95 : impossible 6 0 b0_s95 := by
  apply by_search
  decide +kernel

def b0_s96 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead96 : impossible 6 0 b0_s96 := by
  apply by_search
  decide +kernel

def b0_s97 : List Sig := [b0_w2,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead97 : impossible 6 0 b0_s97 := by
  apply by_search
  decide +kernel

def b0_s98 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead98 : impossible 6 0 b0_s98 := by
  apply by_search
  decide +kernel

def b0_s99 : List Sig := [b0_w2,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead99 : impossible 6 0 b0_s99 := by
  apply by_search
  decide +kernel

def b0_s100 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead100 : impossible 6 0 b0_s100 := by
  apply by_search
  decide +kernel

def b0_s69 : List Sig := [b0_w2,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead69 : impossible 7 0 b0_s69 := by
  apply reject_branch 6 0 b0_s69 [] [[b0_w20,raw4,raw3,raw1,raw2,raw0],[b0_w20,b0_w2,raw4,raw3,raw1,raw2,raw0],[b0_w32,raw4,raw3,raw1,raw2,raw0],[b0_w32,b0_w2,raw4,raw3,raw1,raw2,raw0],[b0_w33,raw2,raw3,raw4,raw1,raw0],[b0_w33,b0_w2,raw2,raw3,raw4,raw1,raw0],[b0_w34,raw2,raw3,raw4,raw1,raw0],[b0_w34,b0_w2,raw2,raw3,raw4,raw1,raw0],[b0_w35,raw0,raw3,raw4,raw1,raw2],[b0_w35,b0_w2,raw0,raw3,raw4,raw1,raw2],[b0_w36,raw0,raw3,raw4,raw1,raw2],[b0_w36,b0_w2,raw0,raw3,raw4,raw1,raw2],[b0_w0,raw3,raw4,b0_w2,raw1,raw2,raw0],[b0_w1,raw3,raw4,b0_w2,raw1,raw2,raw0],[b0_w3,b0_w2,raw4,raw2,raw0],[b0_w3,raw3,b0_w2,raw4,raw2,raw0],[b0_w3,raw1,b0_w2,raw4,raw2,raw0],[b0_w3,raw3,raw1,b0_w2,raw4,raw2,raw0],[b0_w4,raw3,raw2,b0_w2,raw4,raw1,raw0],[b0_w5,raw3,raw2,b0_w2,raw4,raw1,raw0],[b0_w6,raw3,raw0,b0_w2,raw4,raw1,raw2],[b0_w7,raw3,raw0,b0_w2,raw4,raw1,raw2],[b0_w8,raw4,raw1,b0_w2,raw3,raw2,raw0],[b0_w9,raw4,raw1,b0_w2,raw3,raw2,raw0],[b0_w10,raw4,raw2,b0_w2,raw3,raw1,raw0],[b0_w11,raw4,raw2,b0_w2,raw3,raw1,raw0],[b0_w12,raw4,raw0,b0_w2,raw3,raw1,raw2],[b0_w13,raw4,raw0,b0_w2,raw3,raw1,raw2],[b0_w14,raw1,raw2,b0_w2,raw3,raw4,raw0],[b0_w15,raw1,raw2,b0_w2,raw3,raw4,raw0],[b0_w16,raw1,raw0,b0_w2,raw3,raw4,raw2],[b0_w17,raw1,raw0,b0_w2,raw3,raw4,raw2],[b0_w18,raw2,raw0,b0_w2,raw3,raw4,raw1],[b0_w19,raw2,raw0,b0_w2,raw3,raw4,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead2
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead70
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead71
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead72
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead73
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead74
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead75
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead76
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead77
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead78
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead79
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead80
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead18
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead37
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead81
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead82
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead83
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead84
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead85
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead86
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead87
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead88
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead89
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead90
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead91
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead92
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead93
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead94
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead95
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead96
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead97
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead98
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead99
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead100
  · decide +kernel

def b0_s102 : List Sig := [b0_w4,raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead102 : impossible 6 0 b0_s102 := by
  apply by_search
  decide +kernel

def b0_s103 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead103 : impossible 6 0 b0_s103 := by
  apply by_search
  decide +kernel

def b0_s104 : List Sig := [b0_w6,raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead104 : impossible 6 0 b0_s104 := by
  apply by_search
  decide +kernel

def b0_s105 : List Sig := [raw4,raw1,b0_w3,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead105 : impossible 6 0 b0_s105 := by
  apply by_search
  decide +kernel

def b0_s106 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead106 : impossible 6 0 b0_s106 := by
  apply by_search
  decide +kernel

def b0_s107 : List Sig := [b0_w8,raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead107 : impossible 6 0 b0_s107 := by
  apply by_search
  decide +kernel

def b0_s108 : List Sig := [raw3,raw4,raw1,b0_w3,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead108 : impossible 6 0 b0_s108 := by
  apply by_search
  decide +kernel

def b0_s109 : List Sig := [raw3,b0_w37,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead109 : impossible 6 0 b0_s109 := by
  apply by_search
  decide +kernel

def b0_s110 : List Sig := [raw3,b0_w37,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead110 : impossible 6 0 b0_s110 := by
  apply by_search
  decide +kernel

def b0_s111 : List Sig := [raw3,raw4,raw1,b0_w3,b0_w27,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead111 : impossible 6 0 b0_s111 := by
  apply by_search
  decide +kernel

def b0_s112 : List Sig := [b0_w10,raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead112 : impossible 6 0 b0_s112 := by
  apply by_search
  decide +kernel

def b0_s113 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead113 : impossible 6 0 b0_s113 := by
  apply by_search
  decide +kernel

def b0_s114 : List Sig := [b0_w12,raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead114 : impossible 6 0 b0_s114 := by
  apply by_search
  decide +kernel

def b0_s115 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead115 : impossible 6 0 b0_s115 := by
  apply by_search
  decide +kernel

def b0_s116 : List Sig := [b0_w14,raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead116 : impossible 6 0 b0_s116 := by
  apply by_search
  decide +kernel

def b0_s117 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead117 : impossible 6 0 b0_s117 := by
  apply by_search
  decide +kernel

def b0_s118 : List Sig := [raw3,raw4,b0_w16,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead118 : impossible 6 0 b0_s118 := by
  apply by_search
  decide +kernel

def b0_s119 : List Sig := [raw3,raw4,b0_w3,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead119 : impossible 6 0 b0_s119 := by
  apply by_search
  decide +kernel

def b0_s120 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead120 : impossible 6 0 b0_s120 := by
  apply by_search
  decide +kernel

def b0_s121 : List Sig := [b0_w38,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead121 : impossible 6 0 b0_s121 := by
  apply by_search
  decide +kernel

def b0_s122 : List Sig := [b0_w38,raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead122 : impossible 6 0 b0_s122 := by
  apply by_search
  decide +kernel

def b0_s123 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w39]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead123 : impossible 6 0 b0_s123 := by
  apply by_search
  decide +kernel

def b0_s124 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,raw0,b0_w39]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead124 : impossible 6 0 b0_s124 := by
  apply by_search
  decide +kernel

def b0_s125 : List Sig := [raw3,raw4,b0_w40,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead125 : impossible 6 0 b0_s125 := by
  apply by_search
  decide +kernel

def b0_s126 : List Sig := [raw3,raw4,b0_w40,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead126 : impossible 6 0 b0_s126 := by
  apply by_search
  decide +kernel

def b0_s127 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w41]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead127 : impossible 6 0 b0_s127 := by
  apply by_search
  decide +kernel

def b0_s128 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,raw0,b0_w41]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead128 : impossible 6 0 b0_s128 := by
  apply by_search
  decide +kernel

def b0_s129 : List Sig := [raw3,raw4,raw1,b0_w3,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead129 : impossible 6 0 b0_s129 := by
  apply by_search
  decide +kernel

def b0_s130 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead130 : impossible 6 0 b0_s130 := by
  apply by_search
  decide +kernel

def b0_s101 : List Sig := [raw3,raw4,raw1,b0_w3,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead101 : impossible 7 0 b0_s101 := by
  apply reject_branch 6 0 b0_s101 [] [[b0_w0,raw3,raw4,raw1,b0_w3,raw2,raw0],[b0_w1,raw3,raw4,raw1,b0_w3,raw2,raw0],[b0_w2,raw4,b0_w3,raw2,raw0],[b0_w2,raw3,raw4,b0_w3,raw2,raw0],[b0_w2,raw1,raw4,b0_w3,raw2,raw0],[b0_w2,raw3,raw1,raw4,b0_w3,raw2,raw0],[b0_w4,raw3,raw2,raw4,raw1,b0_w3,raw0],[b0_w5,raw3,raw2,raw4,raw1,b0_w3,raw0],[b0_w6,raw3,raw0,raw4,raw1,b0_w3,raw2],[b0_w7,raw0,raw4,raw1,b0_w3,raw2],[b0_w7,raw3,raw0,raw4,raw1,b0_w3,raw2],[b0_w8,raw4,raw1,raw3,b0_w3,raw2,raw0],[b0_w9,raw4,raw1,raw3,b0_w3,raw2,raw0],[b0_w37,raw4,raw3,raw1,raw2,raw0],[b0_w37,raw4,b0_w3,raw3,raw1,raw2,raw0],[b0_w27,raw4,raw3,raw1,raw2,raw0],[b0_w27,raw4,b0_w3,raw3,raw1,raw2,raw0],[b0_w10,raw4,raw2,raw3,raw1,b0_w3,raw0],[b0_w11,raw4,raw2,raw3,raw1,b0_w3,raw0],[b0_w12,raw4,raw0,raw3,raw1,b0_w3,raw2],[b0_w13,raw4,raw0,raw3,raw1,b0_w3,raw2],[b0_w14,raw1,raw2,raw3,raw4,b0_w3,raw0],[b0_w15,raw1,raw2,raw3,raw4,b0_w3,raw0],[b0_w16,raw1,raw0,raw3,raw4,b0_w3,raw2],[b0_w17,raw0,raw3,raw4,b0_w3,raw2],[b0_w17,raw1,raw0,raw3,raw4,b0_w3,raw2],[b0_w38,raw2,raw3,raw4,raw1,raw0],[b0_w38,b0_w3,raw2,raw3,raw4,raw1,raw0],[b0_w39,raw2,raw3,raw4,raw1,raw0],[b0_w39,b0_w3,raw2,raw3,raw4,raw1,raw0],[b0_w40,raw0,raw3,raw4,raw1,raw2],[b0_w40,b0_w3,raw0,raw3,raw4,raw1,raw2],[b0_w41,raw0,raw3,raw4,raw1,raw2],[b0_w41,b0_w3,raw0,raw3,raw4,raw1,raw2],[b0_w18,raw2,raw0,raw3,raw4,raw1,b0_w3],[b0_w19,raw2,raw0,raw3,raw4,raw1,b0_w3]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead19
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead38
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead81
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead82
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead83
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead84
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead102
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead103
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead104
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead105
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead106
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead107
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead108
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead109
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead110
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead53
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead111
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead112
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead113
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead114
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead115
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead116
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead117
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead118
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead119
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead120
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead121
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead122
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead123
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead124
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead125
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead126
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead127
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead128
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead129
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead130
  · decide +kernel

def b0_s132 : List Sig := [b0_w22,b0_w4,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead132 : impossible 6 0 b0_s132 := by
  apply by_search
  decide +kernel

def b0_s133 : List Sig := [raw3,raw4,b0_w42,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead133 : impossible 6 0 b0_s133 := by
  apply by_search
  decide +kernel

def b0_s134 : List Sig := [b0_w4,raw3,raw4,b0_w42,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead134 : impossible 6 0 b0_s134 := by
  apply by_search
  decide +kernel

def b0_s135 : List Sig := [b0_w33,b0_w4,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead135 : impossible 6 0 b0_s135 := by
  apply by_search
  decide +kernel

def b0_s136 : List Sig := [raw3,raw4,raw1,b0_w43,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead136 : impossible 6 0 b0_s136 := by
  apply by_search
  decide +kernel

def b0_s137 : List Sig := [b0_w4,raw3,raw4,raw1,b0_w43,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead137 : impossible 6 0 b0_s137 := by
  apply by_search
  decide +kernel

def b0_s138 : List Sig := [b0_w44,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead138 : impossible 6 0 b0_s138 := by
  apply by_search
  decide +kernel

def b0_s139 : List Sig := [b0_w44,b0_w4,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead139 : impossible 6 0 b0_s139 := by
  apply by_search
  decide +kernel

def b0_s140 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w45]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead140 : impossible 6 0 b0_s140 := by
  apply by_search
  decide +kernel

def b0_s141 : List Sig := [b0_w4,raw3,raw4,raw1,raw2,raw0,b0_w45]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead141 : impossible 6 0 b0_s141 := by
  apply by_search
  decide +kernel

def b0_s142 : List Sig := [b0_w4,raw4,raw1,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead142 : impossible 6 0 b0_s142 := by
  apply by_search
  decide +kernel

def b0_s143 : List Sig := [b0_w4,raw3,raw4,raw1,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead143 : impossible 6 0 b0_s143 := by
  apply by_search
  decide +kernel

def b0_s144 : List Sig := [b0_w4,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead144 : impossible 6 0 b0_s144 := by
  apply by_search
  decide +kernel

def b0_s145 : List Sig := [b0_w4,raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead145 : impossible 6 0 b0_s145 := by
  apply by_search
  decide +kernel

def b0_s146 : List Sig := [b0_w6,b0_w4,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead146 : impossible 6 0 b0_s146 := by
  apply by_search
  decide +kernel

def b0_s147 : List Sig := [b0_w4,raw3,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead147 : impossible 6 0 b0_s147 := by
  apply by_search
  decide +kernel

def b0_s148 : List Sig := [b0_w8,b0_w4,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead148 : impossible 6 0 b0_s148 := by
  apply by_search
  decide +kernel

def b0_s149 : List Sig := [b0_w4,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead149 : impossible 6 0 b0_s149 := by
  apply by_search
  decide +kernel

def b0_s150 : List Sig := [b0_w4,b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead150 : impossible 6 0 b0_s150 := by
  apply by_search
  decide +kernel

def b0_s151 : List Sig := [b0_w4,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead151 : impossible 6 0 b0_s151 := by
  apply by_search
  decide +kernel

def b0_s152 : List Sig := [b0_w12,b0_w4,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead152 : impossible 6 0 b0_s152 := by
  apply by_search
  decide +kernel

def b0_s153 : List Sig := [b0_w4,raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead153 : impossible 6 0 b0_s153 := by
  apply by_search
  decide +kernel

def b0_s154 : List Sig := [b0_w14,b0_w4,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead154 : impossible 6 0 b0_s154 := by
  apply by_search
  decide +kernel

def b0_s155 : List Sig := [b0_w4,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead155 : impossible 6 0 b0_s155 := by
  apply by_search
  decide +kernel

def b0_s156 : List Sig := [b0_w4,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead156 : impossible 6 0 b0_s156 := by
  apply by_search
  decide +kernel

def b0_s157 : List Sig := [b0_w4,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead157 : impossible 6 0 b0_s157 := by
  apply by_search
  decide +kernel

def b0_s158 : List Sig := [b0_w4,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead158 : impossible 6 0 b0_s158 := by
  apply by_search
  decide +kernel

def b0_s159 : List Sig := [b0_w4,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead159 : impossible 6 0 b0_s159 := by
  apply by_search
  decide +kernel

def b0_s131 : List Sig := [b0_w4,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead131 : impossible 7 0 b0_s131 := by
  apply reject_branch 6 0 b0_s131 [] [[b0_w22,raw4,raw3,raw1,raw2,raw0],[b0_w22,b0_w4,raw4,raw3,raw1,raw2,raw0],[b0_w42,raw4,raw3,raw1,raw2,raw0],[b0_w42,b0_w4,raw4,raw3,raw1,raw2,raw0],[b0_w33,raw1,raw3,raw4,raw2,raw0],[b0_w33,b0_w4,raw1,raw3,raw4,raw2,raw0],[b0_w43,raw1,raw3,raw4,raw2,raw0],[b0_w43,b0_w4,raw1,raw3,raw4,raw2,raw0],[b0_w44,raw0,raw3,raw4,raw1,raw2],[b0_w44,b0_w4,raw0,raw3,raw4,raw1,raw2],[b0_w45,raw0,raw3,raw4,raw1,raw2],[b0_w45,b0_w4,raw0,raw3,raw4,raw1,raw2],[b0_w0,raw3,raw4,b0_w4,raw1,raw2,raw0],[b0_w1,raw3,raw4,b0_w4,raw1,raw2,raw0],[b0_w2,raw3,raw1,b0_w4,raw4,raw2,raw0],[b0_w3,raw3,raw1,b0_w4,raw4,raw2,raw0],[b0_w5,b0_w4,raw4,raw1,raw0],[b0_w5,raw3,b0_w4,raw4,raw1,raw0],[b0_w5,raw2,b0_w4,raw4,raw1,raw0],[b0_w5,raw3,raw2,b0_w4,raw4,raw1,raw0],[b0_w6,raw3,raw0,b0_w4,raw4,raw1,raw2],[b0_w7,raw3,raw0,b0_w4,raw4,raw1,raw2],[b0_w8,raw4,raw1,b0_w4,raw3,raw2,raw0],[b0_w9,raw4,raw1,b0_w4,raw3,raw2,raw0],[b0_w10,raw4,raw2,b0_w4,raw3,raw1,raw0],[b0_w11,raw4,raw2,b0_w4,raw3,raw1,raw0],[b0_w12,raw4,raw0,b0_w4,raw3,raw1,raw2],[b0_w13,raw4,raw0,b0_w4,raw3,raw1,raw2],[b0_w14,raw1,raw2,b0_w4,raw3,raw4,raw0],[b0_w15,raw1,raw2,b0_w4,raw3,raw4,raw0],[b0_w16,raw1,raw0,b0_w4,raw3,raw4,raw2],[b0_w17,raw1,raw0,b0_w4,raw3,raw4,raw2],[b0_w18,raw2,raw0,b0_w4,raw3,raw4,raw1],[b0_w19,raw2,raw0,b0_w4,raw3,raw4,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead6
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead132
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead133
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead134
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead73
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead135
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead136
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead137
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead138
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead139
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead140
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead141
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead20
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead39
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead85
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead102
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead142
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead143
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead144
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead145
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead146
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead147
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead148
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead149
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead150
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead151
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead152
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead153
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead154
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead155
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead156
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead157
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead158
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead159
  · decide +kernel

def b0_s161 : List Sig := [b0_w6,raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead161 : impossible 6 0 b0_s161 := by
  apply by_search
  decide +kernel

def b0_s162 : List Sig := [raw4,raw1,raw2,b0_w5,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead162 : impossible 6 0 b0_s162 := by
  apply by_search
  decide +kernel

def b0_s163 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead163 : impossible 6 0 b0_s163 := by
  apply by_search
  decide +kernel

def b0_s164 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead164 : impossible 6 0 b0_s164 := by
  apply by_search
  decide +kernel

def b0_s165 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead165 : impossible 6 0 b0_s165 := by
  apply by_search
  decide +kernel

def b0_s166 : List Sig := [b0_w10,raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead166 : impossible 6 0 b0_s166 := by
  apply by_search
  decide +kernel

def b0_s167 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead167 : impossible 6 0 b0_s167 := by
  apply by_search
  decide +kernel

def b0_s168 : List Sig := [raw3,b0_w46,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead168 : impossible 6 0 b0_s168 := by
  apply by_search
  decide +kernel

def b0_s169 : List Sig := [raw3,b0_w46,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead169 : impossible 6 0 b0_s169 := by
  apply by_search
  decide +kernel

def b0_s170 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,b0_w29,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead170 : impossible 6 0 b0_s170 := by
  apply by_search
  decide +kernel

def b0_s171 : List Sig := [b0_w12,raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead171 : impossible 6 0 b0_s171 := by
  apply by_search
  decide +kernel

def b0_s172 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead172 : impossible 6 0 b0_s172 := by
  apply by_search
  decide +kernel

def b0_s173 : List Sig := [b0_w14,raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead173 : impossible 6 0 b0_s173 := by
  apply by_search
  decide +kernel

def b0_s174 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead174 : impossible 6 0 b0_s174 := by
  apply by_search
  decide +kernel

def b0_s175 : List Sig := [b0_w47,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead175 : impossible 6 0 b0_s175 := by
  apply by_search
  decide +kernel

def b0_s176 : List Sig := [b0_w47,raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead176 : impossible 6 0 b0_s176 := by
  apply by_search
  decide +kernel

def b0_s177 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,raw0,b0_w39]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead177 : impossible 6 0 b0_s177 := by
  apply by_search
  decide +kernel

def b0_s178 : List Sig := [raw3,raw4,b0_w16,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead178 : impossible 6 0 b0_s178 := by
  apply by_search
  decide +kernel

def b0_s179 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead179 : impossible 6 0 b0_s179 := by
  apply by_search
  decide +kernel

def b0_s180 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead180 : impossible 6 0 b0_s180 := by
  apply by_search
  decide +kernel

def b0_s181 : List Sig := [raw3,raw4,raw1,b0_w5,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead181 : impossible 6 0 b0_s181 := by
  apply by_search
  decide +kernel

def b0_s182 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead182 : impossible 6 0 b0_s182 := by
  apply by_search
  decide +kernel

def b0_s183 : List Sig := [raw3,raw4,raw1,b0_w48,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead183 : impossible 6 0 b0_s183 := by
  apply by_search
  decide +kernel

def b0_s184 : List Sig := [raw3,raw4,raw1,b0_w48,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead184 : impossible 6 0 b0_s184 := by
  apply by_search
  decide +kernel

def b0_s185 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w49]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead185 : impossible 6 0 b0_s185 := by
  apply by_search
  decide +kernel

def b0_s186 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,raw0,b0_w49]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead186 : impossible 6 0 b0_s186 := by
  apply by_search
  decide +kernel

def b0_s160 : List Sig := [raw3,raw4,raw1,raw2,b0_w5,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead160 : impossible 7 0 b0_s160 := by
  apply reject_branch 6 0 b0_s160 [] [[b0_w0,raw3,raw4,raw1,raw2,b0_w5,raw0],[b0_w1,raw3,raw4,raw1,raw2,b0_w5,raw0],[b0_w2,raw3,raw1,raw4,raw2,b0_w5,raw0],[b0_w3,raw3,raw1,raw4,raw2,b0_w5,raw0],[b0_w4,raw4,raw1,b0_w5,raw0],[b0_w4,raw3,raw4,raw1,b0_w5,raw0],[b0_w4,raw2,raw4,raw1,b0_w5,raw0],[b0_w4,raw3,raw2,raw4,raw1,b0_w5,raw0],[b0_w6,raw3,raw0,raw4,raw1,raw2,b0_w5],[b0_w7,raw0,raw4,raw1,raw2,b0_w5],[b0_w7,raw3,raw0,raw4,raw1,raw2,b0_w5],[b0_w8,raw4,raw1,raw3,raw2,b0_w5,raw0],[b0_w9,raw4,raw1,raw3,raw2,b0_w5,raw0],[b0_w10,raw4,raw2,raw3,raw1,b0_w5,raw0],[b0_w11,raw4,raw2,raw3,raw1,b0_w5,raw0],[b0_w46,raw4,raw3,raw1,raw2,raw0],[b0_w46,raw4,b0_w5,raw3,raw1,raw2,raw0],[b0_w29,raw4,raw3,raw1,raw2,raw0],[b0_w29,raw4,b0_w5,raw3,raw1,raw2,raw0],[b0_w12,raw4,raw0,raw3,raw1,raw2,b0_w5],[b0_w13,raw4,raw0,raw3,raw1,raw2,b0_w5],[b0_w14,raw1,raw2,raw3,raw4,b0_w5,raw0],[b0_w15,raw1,raw2,raw3,raw4,b0_w5,raw0],[b0_w47,raw1,raw3,raw4,raw2,raw0],[b0_w47,raw1,b0_w5,raw3,raw4,raw2,raw0],[b0_w39,raw1,raw3,raw4,raw2,raw0],[b0_w39,raw1,b0_w5,raw3,raw4,raw2,raw0],[b0_w16,raw1,raw0,raw3,raw4,raw2,b0_w5],[b0_w17,raw1,raw0,raw3,raw4,raw2,b0_w5],[b0_w18,raw2,raw0,raw3,raw4,raw1,b0_w5],[b0_w19,raw0,raw3,raw4,raw1,b0_w5],[b0_w19,raw2,raw0,raw3,raw4,raw1,b0_w5],[b0_w48,raw0,raw3,raw4,raw1,raw2],[b0_w48,b0_w5,raw0,raw3,raw4,raw1,raw2],[b0_w49,raw0,raw3,raw4,raw1,raw2],[b0_w49,b0_w5,raw0,raw3,raw4,raw1,raw2]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead21
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead40
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead86
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead103
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead142
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead143
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead144
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead145
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead161
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead162
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead163
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead164
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead165
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead166
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead167
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead168
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead169
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead57
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead170
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead171
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead172
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead173
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead174
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead175
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead176
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead123
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead177
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead178
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead179
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead180
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead181
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead182
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead183
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead184
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead185
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead186
  · decide +kernel

def b0_s188 : List Sig := [b0_w24,b0_w6,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead188 : impossible 6 0 b0_s188 := by
  apply by_search
  decide +kernel

def b0_s189 : List Sig := [raw3,b0_w50,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead189 : impossible 6 0 b0_s189 := by
  apply by_search
  decide +kernel

def b0_s190 : List Sig := [b0_w6,raw3,b0_w50,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead190 : impossible 6 0 b0_s190 := by
  apply by_search
  decide +kernel

def b0_s191 : List Sig := [raw3,raw4,b0_w50,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead191 : impossible 6 0 b0_s191 := by
  apply by_search
  decide +kernel

def b0_s192 : List Sig := [b0_w6,raw3,raw4,b0_w50,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead192 : impossible 6 0 b0_s192 := by
  apply by_search
  decide +kernel

def b0_s193 : List Sig := [b0_w35,b0_w6,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead193 : impossible 6 0 b0_s193 := by
  apply by_search
  decide +kernel

def b0_s194 : List Sig := [raw3,raw4,b0_w51,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead194 : impossible 6 0 b0_s194 := by
  apply by_search
  decide +kernel

def b0_s195 : List Sig := [b0_w6,raw3,raw4,b0_w51,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead195 : impossible 6 0 b0_s195 := by
  apply by_search
  decide +kernel

def b0_s196 : List Sig := [raw3,raw4,raw1,b0_w51,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead196 : impossible 6 0 b0_s196 := by
  apply by_search
  decide +kernel

def b0_s197 : List Sig := [b0_w6,raw3,raw4,raw1,b0_w51,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead197 : impossible 6 0 b0_s197 := by
  apply by_search
  decide +kernel

def b0_s198 : List Sig := [b0_w44,b0_w6,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead198 : impossible 6 0 b0_s198 := by
  apply by_search
  decide +kernel

def b0_s199 : List Sig := [raw3,raw4,raw1,b0_w52,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead199 : impossible 6 0 b0_s199 := by
  apply by_search
  decide +kernel

def b0_s200 : List Sig := [b0_w6,raw3,raw4,raw1,b0_w52,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead200 : impossible 6 0 b0_s200 := by
  apply by_search
  decide +kernel

def b0_s201 : List Sig := [raw3,raw4,raw1,raw2,b0_w52,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead201 : impossible 6 0 b0_s201 := by
  apply by_search
  decide +kernel

def b0_s202 : List Sig := [b0_w6,raw3,raw4,raw1,raw2,b0_w52,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead202 : impossible 6 0 b0_s202 := by
  apply by_search
  decide +kernel

def b0_s203 : List Sig := [b0_w6,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead203 : impossible 6 0 b0_s203 := by
  apply by_search
  decide +kernel

def b0_s204 : List Sig := [b0_w6,raw3,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead204 : impossible 6 0 b0_s204 := by
  apply by_search
  decide +kernel

def b0_s205 : List Sig := [b0_w6,b0_w8,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead205 : impossible 6 0 b0_s205 := by
  apply by_search
  decide +kernel

def b0_s206 : List Sig := [b0_w6,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead206 : impossible 6 0 b0_s206 := by
  apply by_search
  decide +kernel

def b0_s207 : List Sig := [b0_w6,b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead207 : impossible 6 0 b0_s207 := by
  apply by_search
  decide +kernel

def b0_s208 : List Sig := [b0_w6,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead208 : impossible 6 0 b0_s208 := by
  apply by_search
  decide +kernel

def b0_s209 : List Sig := [b0_w6,b0_w12,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead209 : impossible 6 0 b0_s209 := by
  apply by_search
  decide +kernel

def b0_s210 : List Sig := [b0_w6,raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead210 : impossible 6 0 b0_s210 := by
  apply by_search
  decide +kernel

def b0_s211 : List Sig := [b0_w6,b0_w14,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead211 : impossible 6 0 b0_s211 := by
  apply by_search
  decide +kernel

def b0_s212 : List Sig := [b0_w6,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead212 : impossible 6 0 b0_s212 := by
  apply by_search
  decide +kernel

def b0_s213 : List Sig := [b0_w6,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead213 : impossible 6 0 b0_s213 := by
  apply by_search
  decide +kernel

def b0_s214 : List Sig := [b0_w6,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead214 : impossible 6 0 b0_s214 := by
  apply by_search
  decide +kernel

def b0_s215 : List Sig := [b0_w6,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead215 : impossible 6 0 b0_s215 := by
  apply by_search
  decide +kernel

def b0_s216 : List Sig := [b0_w6,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead216 : impossible 6 0 b0_s216 := by
  apply by_search
  decide +kernel

def b0_s187 : List Sig := [b0_w6,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead187 : impossible 7 0 b0_s187 := by
  apply reject_branch 6 0 b0_s187 [] [[b0_w24,raw4,raw3,raw1,raw2,raw0],[b0_w24,b0_w6,raw4,raw3,raw1,raw2,raw0],[b0_w50,raw3,raw1,raw2,raw0],[b0_w50,b0_w6,raw3,raw1,raw2,raw0],[b0_w50,raw4,raw3,raw1,raw2,raw0],[b0_w50,b0_w6,raw4,raw3,raw1,raw2,raw0],[b0_w35,raw1,raw3,raw4,raw2,raw0],[b0_w35,b0_w6,raw1,raw3,raw4,raw2,raw0],[b0_w51,raw3,raw4,raw2,raw0],[b0_w51,b0_w6,raw3,raw4,raw2,raw0],[b0_w51,raw1,raw3,raw4,raw2,raw0],[b0_w51,b0_w6,raw1,raw3,raw4,raw2,raw0],[b0_w44,raw2,raw3,raw4,raw1,raw0],[b0_w44,b0_w6,raw2,raw3,raw4,raw1,raw0],[b0_w52,raw3,raw4,raw1,raw0],[b0_w52,b0_w6,raw3,raw4,raw1,raw0],[b0_w52,raw2,raw3,raw4,raw1,raw0],[b0_w52,b0_w6,raw2,raw3,raw4,raw1,raw0],[b0_w0,raw3,raw4,b0_w6,raw1,raw2,raw0],[b0_w1,raw3,raw4,b0_w6,raw1,raw2,raw0],[b0_w2,raw3,raw1,b0_w6,raw4,raw2,raw0],[b0_w3,raw3,raw1,b0_w6,raw4,raw2,raw0],[b0_w4,raw3,raw2,b0_w6,raw4,raw1,raw0],[b0_w5,raw3,raw2,b0_w6,raw4,raw1,raw0],[b0_w7,raw0,b0_w6,raw4,raw1,raw2],[b0_w7,raw3,raw0,b0_w6,raw4,raw1,raw2],[b0_w8,raw4,raw1,b0_w6,raw3,raw2,raw0],[b0_w9,raw4,raw1,b0_w6,raw3,raw2,raw0],[b0_w10,raw4,raw2,b0_w6,raw3,raw1,raw0],[b0_w11,raw4,raw2,b0_w6,raw3,raw1,raw0],[b0_w12,raw4,raw0,b0_w6,raw3,raw1,raw2],[b0_w13,raw4,raw0,b0_w6,raw3,raw1,raw2],[b0_w14,raw1,raw2,b0_w6,raw3,raw4,raw0],[b0_w15,raw1,raw2,b0_w6,raw3,raw4,raw0],[b0_w16,raw1,raw0,b0_w6,raw3,raw4,raw2],[b0_w17,raw1,raw0,b0_w6,raw3,raw4,raw2],[b0_w18,raw2,raw0,b0_w6,raw3,raw4,raw1],[b0_w19,raw2,raw0,b0_w6,raw3,raw4,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead10
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead188
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead189
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead190
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead191
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead192
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead77
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead193
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead194
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead195
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead196
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead197
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead138
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead198
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead199
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead200
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead201
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead202
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead22
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead41
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead87
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead104
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead146
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead161
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead203
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead204
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead205
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead206
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead207
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead208
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead209
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead210
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead211
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead212
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead213
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead214
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead215
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead216
  · decide +kernel

def b0_s218 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead218 : impossible 6 0 b0_s218 := by
  apply by_search
  decide +kernel

def b0_s219 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead219 : impossible 6 0 b0_s219 := by
  apply by_search
  decide +kernel

def b0_s220 : List Sig := [b0_w10,raw3,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead220 : impossible 6 0 b0_s220 := by
  apply by_search
  decide +kernel

def b0_s221 : List Sig := [raw3,raw4,raw1,raw2,b0_w11,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead221 : impossible 6 0 b0_s221 := by
  apply by_search
  decide +kernel

def b0_s222 : List Sig := [b0_w12,raw3,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead222 : impossible 6 0 b0_s222 := by
  apply by_search
  decide +kernel

def b0_s223 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w7,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead223 : impossible 6 0 b0_s223 := by
  apply by_search
  decide +kernel

def b0_s224 : List Sig := [raw3,b0_w53,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead224 : impossible 6 0 b0_s224 := by
  apply by_search
  decide +kernel

def b0_s225 : List Sig := [raw3,b0_w53,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead225 : impossible 6 0 b0_s225 := by
  apply by_search
  decide +kernel

def b0_s226 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w7,b0_w31]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead226 : impossible 6 0 b0_s226 := by
  apply by_search
  decide +kernel

def b0_s227 : List Sig := [b0_w14,raw3,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead227 : impossible 6 0 b0_s227 := by
  apply by_search
  decide +kernel

def b0_s228 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w15,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead228 : impossible 6 0 b0_s228 := by
  apply by_search
  decide +kernel

def b0_s229 : List Sig := [raw3,raw4,b0_w16,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead229 : impossible 6 0 b0_s229 := by
  apply by_search
  decide +kernel

def b0_s230 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w17,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead230 : impossible 6 0 b0_s230 := by
  apply by_search
  decide +kernel

def b0_s231 : List Sig := [raw3,raw4,b0_w54,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead231 : impossible 6 0 b0_s231 := by
  apply by_search
  decide +kernel

def b0_s232 : List Sig := [raw3,raw4,b0_w54,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead232 : impossible 6 0 b0_s232 := by
  apply by_search
  decide +kernel

def b0_s233 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w7,b0_w41]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead233 : impossible 6 0 b0_s233 := by
  apply by_search
  decide +kernel

def b0_s234 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead234 : impossible 6 0 b0_s234 := by
  apply by_search
  decide +kernel

def b0_s235 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w19,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead235 : impossible 6 0 b0_s235 := by
  apply by_search
  decide +kernel

def b0_s236 : List Sig := [raw3,raw4,raw1,b0_w55,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead236 : impossible 6 0 b0_s236 := by
  apply by_search
  decide +kernel

def b0_s237 : List Sig := [raw3,raw4,raw1,b0_w55,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead237 : impossible 6 0 b0_s237 := by
  apply by_search
  decide +kernel

def b0_s238 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w7,b0_w49]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead238 : impossible 6 0 b0_s238 := by
  apply by_search
  decide +kernel

def b0_s217 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead217 : impossible 7 0 b0_s217 := by
  apply reject_branch 6 0 b0_s217 [] [[b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w7],[b0_w1,raw4,raw1,raw2,raw0,b0_w7],[b0_w1,raw3,raw4,raw1,raw2,raw0,b0_w7],[b0_w2,raw3,raw1,raw4,raw2,raw0,b0_w7],[b0_w3,raw1,raw4,raw2,raw0,b0_w7],[b0_w3,raw3,raw1,raw4,raw2,raw0,b0_w7],[b0_w4,raw3,raw2,raw4,raw1,raw0,b0_w7],[b0_w5,raw2,raw4,raw1,raw0,b0_w7],[b0_w5,raw3,raw2,raw4,raw1,raw0,b0_w7],[b0_w6,raw0,raw4,raw1,raw2,b0_w7],[b0_w6,raw3,raw0,raw4,raw1,raw2,b0_w7],[b0_w8,raw4,raw1,raw3,raw2,raw0,b0_w7],[b0_w9,raw4,raw1,raw3,raw2,raw0,b0_w7],[b0_w10,raw4,raw2,raw3,raw1,raw0,b0_w7],[b0_w11,raw4,raw2,raw3,raw1,raw0,b0_w7],[b0_w12,raw4,raw0,raw3,raw1,raw2,b0_w7],[b0_w13,raw4,raw0,raw3,raw1,raw2,b0_w7],[b0_w53,raw4,raw3,raw1,raw2,raw0],[b0_w53,raw4,b0_w7,raw3,raw1,raw2,raw0],[b0_w31,raw4,raw3,raw1,raw2,raw0],[b0_w31,raw4,b0_w7,raw3,raw1,raw2,raw0],[b0_w14,raw1,raw2,raw3,raw4,raw0,b0_w7],[b0_w15,raw1,raw2,raw3,raw4,raw0,b0_w7],[b0_w16,raw1,raw0,raw3,raw4,raw2,b0_w7],[b0_w17,raw1,raw0,raw3,raw4,raw2,b0_w7],[b0_w54,raw1,raw3,raw4,raw2,raw0],[b0_w54,raw1,b0_w7,raw3,raw4,raw2,raw0],[b0_w41,raw1,raw3,raw4,raw2,raw0],[b0_w41,raw1,b0_w7,raw3,raw4,raw2,raw0],[b0_w18,raw2,raw0,raw3,raw4,raw1,b0_w7],[b0_w19,raw2,raw0,raw3,raw4,raw1,b0_w7],[b0_w55,raw2,raw3,raw4,raw1,raw0],[b0_w55,raw2,b0_w7,raw3,raw4,raw1,raw0],[b0_w49,raw2,raw3,raw4,raw1,raw0],[b0_w49,raw2,b0_w7,raw3,raw4,raw1,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead23
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead42
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead43
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead88
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead105
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead106
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead147
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead162
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead163
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead203
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead204
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead218
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead219
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead220
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead221
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead222
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead223
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead224
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead225
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead61
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead226
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead227
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead228
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead229
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead230
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead231
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead232
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead127
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead233
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead234
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead235
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead236
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead237
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead185
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead238
  · decide +kernel

def b0_s240 : List Sig := [b0_w20,b0_w8,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead240 : impossible 6 0 b0_s240 := by
  apply by_search
  decide +kernel

def b0_s241 : List Sig := [raw3,b0_w56,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead241 : impossible 6 0 b0_s241 := by
  apply by_search
  decide +kernel

def b0_s242 : List Sig := [b0_w8,raw3,b0_w56,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead242 : impossible 6 0 b0_s242 := by
  apply by_search
  decide +kernel

def b0_s243 : List Sig := [b0_w57,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead243 : impossible 6 0 b0_s243 := by
  apply by_search
  decide +kernel

def b0_s244 : List Sig := [b0_w57,b0_w8,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead244 : impossible 6 0 b0_s244 := by
  apply by_search
  decide +kernel

def b0_s245 : List Sig := [raw3,raw4,raw1,raw2,b0_w58,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead245 : impossible 6 0 b0_s245 := by
  apply by_search
  decide +kernel

def b0_s246 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,b0_w58,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead246 : impossible 6 0 b0_s246 := by
  apply by_search
  decide +kernel

def b0_s247 : List Sig := [b0_w59,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead247 : impossible 6 0 b0_s247 := by
  apply by_search
  decide +kernel

def b0_s248 : List Sig := [b0_w59,b0_w8,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead248 : impossible 6 0 b0_s248 := by
  apply by_search
  decide +kernel

def b0_s249 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w60]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead249 : impossible 6 0 b0_s249 := by
  apply by_search
  decide +kernel

def b0_s250 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,raw0,b0_w60]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead250 : impossible 6 0 b0_s250 := by
  apply by_search
  decide +kernel

def b0_s251 : List Sig := [b0_w8,raw3,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead251 : impossible 6 0 b0_s251 := by
  apply by_search
  decide +kernel

def b0_s252 : List Sig := [b0_w8,raw3,raw4,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead252 : impossible 6 0 b0_s252 := by
  apply by_search
  decide +kernel

def b0_s253 : List Sig := [b0_w8,raw3,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead253 : impossible 6 0 b0_s253 := by
  apply by_search
  decide +kernel

def b0_s254 : List Sig := [b0_w8,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead254 : impossible 6 0 b0_s254 := by
  apply by_search
  decide +kernel

def b0_s255 : List Sig := [b0_w8,b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead255 : impossible 6 0 b0_s255 := by
  apply by_search
  decide +kernel

def b0_s256 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead256 : impossible 6 0 b0_s256 := by
  apply by_search
  decide +kernel

def b0_s257 : List Sig := [b0_w12,b0_w8,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead257 : impossible 6 0 b0_s257 := by
  apply by_search
  decide +kernel

def b0_s258 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead258 : impossible 6 0 b0_s258 := by
  apply by_search
  decide +kernel

def b0_s259 : List Sig := [b0_w14,b0_w8,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead259 : impossible 6 0 b0_s259 := by
  apply by_search
  decide +kernel

def b0_s260 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead260 : impossible 6 0 b0_s260 := by
  apply by_search
  decide +kernel

def b0_s261 : List Sig := [b0_w8,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead261 : impossible 6 0 b0_s261 := by
  apply by_search
  decide +kernel

def b0_s262 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead262 : impossible 6 0 b0_s262 := by
  apply by_search
  decide +kernel

def b0_s263 : List Sig := [b0_w8,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead263 : impossible 6 0 b0_s263 := by
  apply by_search
  decide +kernel

def b0_s264 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead264 : impossible 6 0 b0_s264 := by
  apply by_search
  decide +kernel

def b0_s239 : List Sig := [b0_w8,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead239 : impossible 7 0 b0_s239 := by
  apply reject_branch 6 0 b0_s239 [] [[b0_w20,raw3,raw4,raw1,raw2,raw0],[b0_w20,b0_w8,raw3,raw4,raw1,raw2,raw0],[b0_w56,raw3,raw4,raw1,raw2,raw0],[b0_w56,b0_w8,raw3,raw4,raw1,raw2,raw0],[b0_w57,raw2,raw3,raw4,raw1,raw0],[b0_w57,b0_w8,raw2,raw3,raw4,raw1,raw0],[b0_w58,raw2,raw3,raw4,raw1,raw0],[b0_w58,b0_w8,raw2,raw3,raw4,raw1,raw0],[b0_w59,raw0,raw3,raw4,raw1,raw2],[b0_w59,b0_w8,raw0,raw3,raw4,raw1,raw2],[b0_w60,raw0,raw3,raw4,raw1,raw2],[b0_w60,b0_w8,raw0,raw3,raw4,raw1,raw2],[b0_w0,raw3,raw4,b0_w8,raw1,raw2,raw0],[b0_w1,raw3,raw4,b0_w8,raw1,raw2,raw0],[b0_w2,raw3,raw1,b0_w8,raw4,raw2,raw0],[b0_w3,raw3,raw1,b0_w8,raw4,raw2,raw0],[b0_w4,raw3,raw2,b0_w8,raw4,raw1,raw0],[b0_w5,raw3,raw2,b0_w8,raw4,raw1,raw0],[b0_w6,raw3,raw0,b0_w8,raw4,raw1,raw2],[b0_w7,raw3,raw0,b0_w8,raw4,raw1,raw2],[b0_w9,b0_w8,raw3,raw2,raw0],[b0_w9,raw4,b0_w8,raw3,raw2,raw0],[b0_w9,raw1,b0_w8,raw3,raw2,raw0],[b0_w9,raw4,raw1,b0_w8,raw3,raw2,raw0],[b0_w10,raw4,raw2,b0_w8,raw3,raw1,raw0],[b0_w11,raw4,raw2,b0_w8,raw3,raw1,raw0],[b0_w12,raw4,raw0,b0_w8,raw3,raw1,raw2],[b0_w13,raw4,raw0,b0_w8,raw3,raw1,raw2],[b0_w14,raw1,raw2,b0_w8,raw3,raw4,raw0],[b0_w15,raw1,raw2,b0_w8,raw3,raw4,raw0],[b0_w16,raw1,raw0,b0_w8,raw3,raw4,raw2],[b0_w17,raw1,raw0,b0_w8,raw3,raw4,raw2],[b0_w18,raw2,raw0,b0_w8,raw3,raw4,raw1],[b0_w19,raw2,raw0,b0_w8,raw3,raw4,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead2
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead240
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead241
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead242
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead243
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead244
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead245
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead246
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead247
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead248
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead249
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead250
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead24
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead44
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead89
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead107
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead148
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead164
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead205
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead218
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead251
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead252
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead253
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead254
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead255
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead256
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead257
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead258
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead259
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead260
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead261
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead262
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead263
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead264
  · decide +kernel

def b0_s266 : List Sig := [b0_w61,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead266 : impossible 6 0 b0_s266 := by
  apply by_search
  decide +kernel

def b0_s267 : List Sig := [b0_w61,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead267 : impossible 6 0 b0_s267 := by
  apply by_search
  decide +kernel

def b0_s268 : List Sig := [raw3,raw4,raw1,b0_w9,b0_w27,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead268 : impossible 6 0 b0_s268 := by
  apply by_search
  decide +kernel

def b0_s269 : List Sig := [b0_w10,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead269 : impossible 6 0 b0_s269 := by
  apply by_search
  decide +kernel

def b0_s270 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead270 : impossible 6 0 b0_s270 := by
  apply by_search
  decide +kernel

def b0_s271 : List Sig := [b0_w12,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead271 : impossible 6 0 b0_s271 := by
  apply by_search
  decide +kernel

def b0_s272 : List Sig := [raw3,raw1,b0_w9,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead272 : impossible 6 0 b0_s272 := by
  apply by_search
  decide +kernel

def b0_s273 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead273 : impossible 6 0 b0_s273 := by
  apply by_search
  decide +kernel

def b0_s274 : List Sig := [b0_w14,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead274 : impossible 6 0 b0_s274 := by
  apply by_search
  decide +kernel

def b0_s275 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead275 : impossible 6 0 b0_s275 := by
  apply by_search
  decide +kernel

def b0_s276 : List Sig := [raw3,raw4,b0_w16,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead276 : impossible 6 0 b0_s276 := by
  apply by_search
  decide +kernel

def b0_s277 : List Sig := [raw3,raw4,b0_w9,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead277 : impossible 6 0 b0_s277 := by
  apply by_search
  decide +kernel

def b0_s278 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead278 : impossible 6 0 b0_s278 := by
  apply by_search
  decide +kernel

def b0_s279 : List Sig := [b0_w62,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead279 : impossible 6 0 b0_s279 := by
  apply by_search
  decide +kernel

def b0_s280 : List Sig := [b0_w62,raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead280 : impossible 6 0 b0_s280 := by
  apply by_search
  decide +kernel

def b0_s281 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w63]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead281 : impossible 6 0 b0_s281 := by
  apply by_search
  decide +kernel

def b0_s282 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,raw0,b0_w63]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead282 : impossible 6 0 b0_s282 := by
  apply by_search
  decide +kernel

def b0_s283 : List Sig := [raw3,raw4,b0_w64,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead283 : impossible 6 0 b0_s283 := by
  apply by_search
  decide +kernel

def b0_s284 : List Sig := [raw3,raw4,b0_w64,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead284 : impossible 6 0 b0_s284 := by
  apply by_search
  decide +kernel

def b0_s285 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w65]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead285 : impossible 6 0 b0_s285 := by
  apply by_search
  decide +kernel

def b0_s286 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,raw0,b0_w65]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead286 : impossible 6 0 b0_s286 := by
  apply by_search
  decide +kernel

def b0_s287 : List Sig := [raw3,raw4,raw1,b0_w9,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead287 : impossible 6 0 b0_s287 := by
  apply by_search
  decide +kernel

def b0_s288 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead288 : impossible 6 0 b0_s288 := by
  apply by_search
  decide +kernel

def b0_s265 : List Sig := [raw3,raw4,raw1,b0_w9,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead265 : impossible 7 0 b0_s265 := by
  apply reject_branch 6 0 b0_s265 [] [[b0_w0,raw3,raw4,raw1,b0_w9,raw2,raw0],[b0_w1,raw3,raw4,raw1,b0_w9,raw2,raw0],[b0_w2,raw3,raw1,raw4,b0_w9,raw2,raw0],[b0_w3,raw3,raw1,raw4,b0_w9,raw2,raw0],[b0_w61,raw3,raw4,raw1,raw2,raw0],[b0_w61,raw3,b0_w9,raw4,raw1,raw2,raw0],[b0_w27,raw3,raw4,raw1,raw2,raw0],[b0_w27,raw3,b0_w9,raw4,raw1,raw2,raw0],[b0_w4,raw3,raw2,raw4,raw1,b0_w9,raw0],[b0_w5,raw3,raw2,raw4,raw1,b0_w9,raw0],[b0_w6,raw3,raw0,raw4,raw1,b0_w9,raw2],[b0_w7,raw3,raw0,raw4,raw1,b0_w9,raw2],[b0_w8,raw3,b0_w9,raw2,raw0],[b0_w8,raw4,raw3,b0_w9,raw2,raw0],[b0_w8,raw1,raw3,b0_w9,raw2,raw0],[b0_w8,raw4,raw1,raw3,b0_w9,raw2,raw0],[b0_w10,raw4,raw2,raw3,raw1,b0_w9,raw0],[b0_w11,raw4,raw2,raw3,raw1,b0_w9,raw0],[b0_w12,raw4,raw0,raw3,raw1,b0_w9,raw2],[b0_w13,raw0,raw3,raw1,b0_w9,raw2],[b0_w13,raw4,raw0,raw3,raw1,b0_w9,raw2],[b0_w14,raw1,raw2,raw3,raw4,b0_w9,raw0],[b0_w15,raw1,raw2,raw3,raw4,b0_w9,raw0],[b0_w16,raw1,raw0,raw3,raw4,b0_w9,raw2],[b0_w17,raw0,raw3,raw4,b0_w9,raw2],[b0_w17,raw1,raw0,raw3,raw4,b0_w9,raw2],[b0_w62,raw2,raw3,raw4,raw1,raw0],[b0_w62,b0_w9,raw2,raw3,raw4,raw1,raw0],[b0_w63,raw2,raw3,raw4,raw1,raw0],[b0_w63,b0_w9,raw2,raw3,raw4,raw1,raw0],[b0_w64,raw0,raw3,raw4,raw1,raw2],[b0_w64,b0_w9,raw0,raw3,raw4,raw1,raw2],[b0_w65,raw0,raw3,raw4,raw1,raw2],[b0_w65,b0_w9,raw0,raw3,raw4,raw1,raw2],[b0_w18,raw2,raw0,raw3,raw4,raw1,b0_w9],[b0_w19,raw2,raw0,raw3,raw4,raw1,b0_w9]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead25
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead45
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead90
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead108
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead266
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead267
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead53
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead268
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead149
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead165
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead206
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead219
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead251
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead252
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead253
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead254
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead269
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead270
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead271
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead272
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead273
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead274
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead275
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead276
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead277
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead278
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead279
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead280
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead281
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead282
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead283
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead284
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead285
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead286
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead287
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead288
  · decide +kernel

def b0_s290 : List Sig := [b0_w22,b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead290 : impossible 6 0 b0_s290 := by
  apply by_search
  decide +kernel

def b0_s291 : List Sig := [raw3,b0_w66,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead291 : impossible 6 0 b0_s291 := by
  apply by_search
  decide +kernel

def b0_s292 : List Sig := [b0_w10,raw3,b0_w66,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead292 : impossible 6 0 b0_s292 := by
  apply by_search
  decide +kernel

def b0_s293 : List Sig := [b0_w57,b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead293 : impossible 6 0 b0_s293 := by
  apply by_search
  decide +kernel

def b0_s294 : List Sig := [raw3,raw4,raw1,b0_w67,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead294 : impossible 6 0 b0_s294 := by
  apply by_search
  decide +kernel

def b0_s295 : List Sig := [b0_w10,raw3,raw4,raw1,b0_w67,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead295 : impossible 6 0 b0_s295 := by
  apply by_search
  decide +kernel

def b0_s296 : List Sig := [b0_w68,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead296 : impossible 6 0 b0_s296 := by
  apply by_search
  decide +kernel

def b0_s297 : List Sig := [b0_w68,b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead297 : impossible 6 0 b0_s297 := by
  apply by_search
  decide +kernel

def b0_s298 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w69]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead298 : impossible 6 0 b0_s298 := by
  apply by_search
  decide +kernel

def b0_s299 : List Sig := [b0_w10,raw3,raw4,raw1,raw2,raw0,b0_w69]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead299 : impossible 6 0 b0_s299 := by
  apply by_search
  decide +kernel

def b0_s300 : List Sig := [b0_w10,raw3,raw1,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead300 : impossible 6 0 b0_s300 := by
  apply by_search
  decide +kernel

def b0_s301 : List Sig := [b0_w10,raw3,raw4,raw1,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead301 : impossible 6 0 b0_s301 := by
  apply by_search
  decide +kernel

def b0_s302 : List Sig := [b0_w10,raw3,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead302 : impossible 6 0 b0_s302 := by
  apply by_search
  decide +kernel

def b0_s303 : List Sig := [b0_w10,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead303 : impossible 6 0 b0_s303 := by
  apply by_search
  decide +kernel

def b0_s304 : List Sig := [b0_w12,b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead304 : impossible 6 0 b0_s304 := by
  apply by_search
  decide +kernel

def b0_s305 : List Sig := [b0_w10,raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead305 : impossible 6 0 b0_s305 := by
  apply by_search
  decide +kernel

def b0_s306 : List Sig := [b0_w14,b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead306 : impossible 6 0 b0_s306 := by
  apply by_search
  decide +kernel

def b0_s307 : List Sig := [b0_w10,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead307 : impossible 6 0 b0_s307 := by
  apply by_search
  decide +kernel

def b0_s308 : List Sig := [b0_w10,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead308 : impossible 6 0 b0_s308 := by
  apply by_search
  decide +kernel

def b0_s309 : List Sig := [b0_w10,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead309 : impossible 6 0 b0_s309 := by
  apply by_search
  decide +kernel

def b0_s310 : List Sig := [b0_w10,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead310 : impossible 6 0 b0_s310 := by
  apply by_search
  decide +kernel

def b0_s311 : List Sig := [b0_w10,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead311 : impossible 6 0 b0_s311 := by
  apply by_search
  decide +kernel

def b0_s289 : List Sig := [b0_w10,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead289 : impossible 7 0 b0_s289 := by
  apply reject_branch 6 0 b0_s289 [] [[b0_w22,raw3,raw4,raw1,raw2,raw0],[b0_w22,b0_w10,raw3,raw4,raw1,raw2,raw0],[b0_w66,raw3,raw4,raw1,raw2,raw0],[b0_w66,b0_w10,raw3,raw4,raw1,raw2,raw0],[b0_w57,raw1,raw3,raw4,raw2,raw0],[b0_w57,b0_w10,raw1,raw3,raw4,raw2,raw0],[b0_w67,raw1,raw3,raw4,raw2,raw0],[b0_w67,b0_w10,raw1,raw3,raw4,raw2,raw0],[b0_w68,raw0,raw3,raw4,raw1,raw2],[b0_w68,b0_w10,raw0,raw3,raw4,raw1,raw2],[b0_w69,raw0,raw3,raw4,raw1,raw2],[b0_w69,b0_w10,raw0,raw3,raw4,raw1,raw2],[b0_w0,raw3,raw4,b0_w10,raw1,raw2,raw0],[b0_w1,raw3,raw4,b0_w10,raw1,raw2,raw0],[b0_w2,raw3,raw1,b0_w10,raw4,raw2,raw0],[b0_w3,raw3,raw1,b0_w10,raw4,raw2,raw0],[b0_w4,raw3,raw2,b0_w10,raw4,raw1,raw0],[b0_w5,raw3,raw2,b0_w10,raw4,raw1,raw0],[b0_w6,raw3,raw0,b0_w10,raw4,raw1,raw2],[b0_w7,raw3,raw0,b0_w10,raw4,raw1,raw2],[b0_w8,raw4,raw1,b0_w10,raw3,raw2,raw0],[b0_w9,raw4,raw1,b0_w10,raw3,raw2,raw0],[b0_w11,b0_w10,raw3,raw1,raw0],[b0_w11,raw4,b0_w10,raw3,raw1,raw0],[b0_w11,raw2,b0_w10,raw3,raw1,raw0],[b0_w11,raw4,raw2,b0_w10,raw3,raw1,raw0],[b0_w12,raw4,raw0,b0_w10,raw3,raw1,raw2],[b0_w13,raw4,raw0,b0_w10,raw3,raw1,raw2],[b0_w14,raw1,raw2,b0_w10,raw3,raw4,raw0],[b0_w15,raw1,raw2,b0_w10,raw3,raw4,raw0],[b0_w16,raw1,raw0,b0_w10,raw3,raw4,raw2],[b0_w17,raw1,raw0,b0_w10,raw3,raw4,raw2],[b0_w18,raw2,raw0,b0_w10,raw3,raw4,raw1],[b0_w19,raw2,raw0,b0_w10,raw3,raw4,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead6
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead290
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead291
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead292
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead243
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead293
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead294
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead295
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead296
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead297
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead298
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead299
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead26
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead46
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead91
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead112
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead150
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead166
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead207
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead220
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead255
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead269
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead300
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead301
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead302
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead303
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead304
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead305
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead306
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead307
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead308
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead309
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead310
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead311
  · decide +kernel

def b0_s313 : List Sig := [b0_w70,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead313 : impossible 6 0 b0_s313 := by
  apply by_search
  decide +kernel

def b0_s314 : List Sig := [b0_w70,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead314 : impossible 6 0 b0_s314 := by
  apply by_search
  decide +kernel

def b0_s315 : List Sig := [raw3,raw4,raw1,raw2,b0_w11,b0_w29,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead315 : impossible 6 0 b0_s315 := by
  apply by_search
  decide +kernel

def b0_s316 : List Sig := [b0_w12,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead316 : impossible 6 0 b0_s316 := by
  apply by_search
  decide +kernel

def b0_s317 : List Sig := [raw3,raw1,raw2,b0_w11,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead317 : impossible 6 0 b0_s317 := by
  apply by_search
  decide +kernel

def b0_s318 : List Sig := [raw3,raw4,raw1,raw2,b0_w11,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead318 : impossible 6 0 b0_s318 := by
  apply by_search
  decide +kernel

def b0_s319 : List Sig := [b0_w14,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead319 : impossible 6 0 b0_s319 := by
  apply by_search
  decide +kernel

def b0_s320 : List Sig := [raw3,raw4,raw1,raw2,b0_w11,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead320 : impossible 6 0 b0_s320 := by
  apply by_search
  decide +kernel

def b0_s321 : List Sig := [b0_w71,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead321 : impossible 6 0 b0_s321 := by
  apply by_search
  decide +kernel

def b0_s322 : List Sig := [b0_w71,raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead322 : impossible 6 0 b0_s322 := by
  apply by_search
  decide +kernel

def b0_s323 : List Sig := [raw3,raw4,raw1,raw2,b0_w11,raw0,b0_w63]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead323 : impossible 6 0 b0_s323 := by
  apply by_search
  decide +kernel

def b0_s324 : List Sig := [raw3,raw4,b0_w16,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead324 : impossible 6 0 b0_s324 := by
  apply by_search
  decide +kernel

def b0_s325 : List Sig := [raw3,raw4,raw1,raw2,b0_w11,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead325 : impossible 6 0 b0_s325 := by
  apply by_search
  decide +kernel

def b0_s326 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead326 : impossible 6 0 b0_s326 := by
  apply by_search
  decide +kernel

def b0_s327 : List Sig := [raw3,raw4,raw1,b0_w11,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead327 : impossible 6 0 b0_s327 := by
  apply by_search
  decide +kernel

def b0_s328 : List Sig := [raw3,raw4,raw1,raw2,b0_w11,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead328 : impossible 6 0 b0_s328 := by
  apply by_search
  decide +kernel

def b0_s329 : List Sig := [raw3,raw4,raw1,b0_w72,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead329 : impossible 6 0 b0_s329 := by
  apply by_search
  decide +kernel

def b0_s330 : List Sig := [raw3,raw4,raw1,b0_w72,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead330 : impossible 6 0 b0_s330 := by
  apply by_search
  decide +kernel

def b0_s331 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w73]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead331 : impossible 6 0 b0_s331 := by
  apply by_search
  decide +kernel

def b0_s332 : List Sig := [raw3,raw4,raw1,raw2,b0_w11,raw0,b0_w73]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead332 : impossible 6 0 b0_s332 := by
  apply by_search
  decide +kernel

def b0_s312 : List Sig := [raw3,raw4,raw1,raw2,b0_w11,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead312 : impossible 7 0 b0_s312 := by
  apply reject_branch 6 0 b0_s312 [] [[b0_w0,raw3,raw4,raw1,raw2,b0_w11,raw0],[b0_w1,raw3,raw4,raw1,raw2,b0_w11,raw0],[b0_w2,raw3,raw1,raw4,raw2,b0_w11,raw0],[b0_w3,raw3,raw1,raw4,raw2,b0_w11,raw0],[b0_w4,raw3,raw2,raw4,raw1,b0_w11,raw0],[b0_w5,raw3,raw2,raw4,raw1,b0_w11,raw0],[b0_w70,raw3,raw4,raw1,raw2,raw0],[b0_w70,raw3,b0_w11,raw4,raw1,raw2,raw0],[b0_w29,raw3,raw4,raw1,raw2,raw0],[b0_w29,raw3,b0_w11,raw4,raw1,raw2,raw0],[b0_w6,raw3,raw0,raw4,raw1,raw2,b0_w11],[b0_w7,raw3,raw0,raw4,raw1,raw2,b0_w11],[b0_w8,raw4,raw1,raw3,raw2,b0_w11,raw0],[b0_w9,raw4,raw1,raw3,raw2,b0_w11,raw0],[b0_w10,raw3,raw1,b0_w11,raw0],[b0_w10,raw4,raw3,raw1,b0_w11,raw0],[b0_w10,raw2,raw3,raw1,b0_w11,raw0],[b0_w10,raw4,raw2,raw3,raw1,b0_w11,raw0],[b0_w12,raw4,raw0,raw3,raw1,raw2,b0_w11],[b0_w13,raw0,raw3,raw1,raw2,b0_w11],[b0_w13,raw4,raw0,raw3,raw1,raw2,b0_w11],[b0_w14,raw1,raw2,raw3,raw4,b0_w11,raw0],[b0_w15,raw1,raw2,raw3,raw4,b0_w11,raw0],[b0_w71,raw1,raw3,raw4,raw2,raw0],[b0_w71,raw1,b0_w11,raw3,raw4,raw2,raw0],[b0_w63,raw1,raw3,raw4,raw2,raw0],[b0_w63,raw1,b0_w11,raw3,raw4,raw2,raw0],[b0_w16,raw1,raw0,raw3,raw4,raw2,b0_w11],[b0_w17,raw1,raw0,raw3,raw4,raw2,b0_w11],[b0_w18,raw2,raw0,raw3,raw4,raw1,b0_w11],[b0_w19,raw0,raw3,raw4,raw1,b0_w11],[b0_w19,raw2,raw0,raw3,raw4,raw1,b0_w11],[b0_w72,raw0,raw3,raw4,raw1,raw2],[b0_w72,b0_w11,raw0,raw3,raw4,raw1,raw2],[b0_w73,raw0,raw3,raw4,raw1,raw2],[b0_w73,b0_w11,raw0,raw3,raw4,raw1,raw2]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead27
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead47
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead92
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead113
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead151
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead167
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead313
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead314
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead57
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead315
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead208
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead221
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead256
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead270
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead300
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead301
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead302
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead303
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead316
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead317
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead318
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead319
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead320
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead321
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead322
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead281
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead323
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead324
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead325
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead326
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead327
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead328
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead329
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead330
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead331
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead332
  · decide +kernel

def b0_s334 : List Sig := [b0_w24,b0_w12,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead334 : impossible 6 0 b0_s334 := by
  apply by_search
  decide +kernel

def b0_s335 : List Sig := [b0_w74,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead335 : impossible 6 0 b0_s335 := by
  apply by_search
  decide +kernel

def b0_s336 : List Sig := [b0_w12,b0_w74,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead336 : impossible 6 0 b0_s336 := by
  apply by_search
  decide +kernel

def b0_s337 : List Sig := [raw3,b0_w74,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead337 : impossible 6 0 b0_s337 := by
  apply by_search
  decide +kernel

def b0_s338 : List Sig := [b0_w12,raw3,b0_w74,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead338 : impossible 6 0 b0_s338 := by
  apply by_search
  decide +kernel

def b0_s339 : List Sig := [b0_w59,b0_w12,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead339 : impossible 6 0 b0_s339 := by
  apply by_search
  decide +kernel

def b0_s340 : List Sig := [raw3,raw4,b0_w75,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead340 : impossible 6 0 b0_s340 := by
  apply by_search
  decide +kernel

def b0_s341 : List Sig := [b0_w12,raw3,raw4,b0_w75,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead341 : impossible 6 0 b0_s341 := by
  apply by_search
  decide +kernel

def b0_s342 : List Sig := [raw3,raw4,raw1,b0_w75,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead342 : impossible 6 0 b0_s342 := by
  apply by_search
  decide +kernel

def b0_s343 : List Sig := [b0_w12,raw3,raw4,raw1,b0_w75,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead343 : impossible 6 0 b0_s343 := by
  apply by_search
  decide +kernel

def b0_s344 : List Sig := [b0_w68,b0_w12,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead344 : impossible 6 0 b0_s344 := by
  apply by_search
  decide +kernel

def b0_s345 : List Sig := [raw3,raw4,raw1,b0_w76,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead345 : impossible 6 0 b0_s345 := by
  apply by_search
  decide +kernel

def b0_s346 : List Sig := [b0_w12,raw3,raw4,raw1,b0_w76,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead346 : impossible 6 0 b0_s346 := by
  apply by_search
  decide +kernel

def b0_s347 : List Sig := [raw3,raw4,raw1,raw2,b0_w76,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead347 : impossible 6 0 b0_s347 := by
  apply by_search
  decide +kernel

def b0_s348 : List Sig := [b0_w12,raw3,raw4,raw1,raw2,b0_w76,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead348 : impossible 6 0 b0_s348 := by
  apply by_search
  decide +kernel

def b0_s349 : List Sig := [b0_w12,raw3,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead349 : impossible 6 0 b0_s349 := by
  apply by_search
  decide +kernel

def b0_s350 : List Sig := [b0_w12,raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead350 : impossible 6 0 b0_s350 := by
  apply by_search
  decide +kernel

def b0_s351 : List Sig := [b0_w12,b0_w14,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead351 : impossible 6 0 b0_s351 := by
  apply by_search
  decide +kernel

def b0_s352 : List Sig := [b0_w12,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead352 : impossible 6 0 b0_s352 := by
  apply by_search
  decide +kernel

def b0_s353 : List Sig := [b0_w12,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead353 : impossible 6 0 b0_s353 := by
  apply by_search
  decide +kernel

def b0_s354 : List Sig := [b0_w12,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead354 : impossible 6 0 b0_s354 := by
  apply by_search
  decide +kernel

def b0_s355 : List Sig := [b0_w12,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead355 : impossible 6 0 b0_s355 := by
  apply by_search
  decide +kernel

def b0_s356 : List Sig := [b0_w12,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead356 : impossible 6 0 b0_s356 := by
  apply by_search
  decide +kernel

def b0_s333 : List Sig := [b0_w12,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead333 : impossible 7 0 b0_s333 := by
  apply reject_branch 6 0 b0_s333 [] [[b0_w24,raw3,raw4,raw1,raw2,raw0],[b0_w24,b0_w12,raw3,raw4,raw1,raw2,raw0],[b0_w74,raw4,raw1,raw2,raw0],[b0_w74,b0_w12,raw4,raw1,raw2,raw0],[b0_w74,raw3,raw4,raw1,raw2,raw0],[b0_w74,b0_w12,raw3,raw4,raw1,raw2,raw0],[b0_w59,raw1,raw3,raw4,raw2,raw0],[b0_w59,b0_w12,raw1,raw3,raw4,raw2,raw0],[b0_w75,raw3,raw4,raw2,raw0],[b0_w75,b0_w12,raw3,raw4,raw2,raw0],[b0_w75,raw1,raw3,raw4,raw2,raw0],[b0_w75,b0_w12,raw1,raw3,raw4,raw2,raw0],[b0_w68,raw2,raw3,raw4,raw1,raw0],[b0_w68,b0_w12,raw2,raw3,raw4,raw1,raw0],[b0_w76,raw3,raw4,raw1,raw0],[b0_w76,b0_w12,raw3,raw4,raw1,raw0],[b0_w76,raw2,raw3,raw4,raw1,raw0],[b0_w76,b0_w12,raw2,raw3,raw4,raw1,raw0],[b0_w0,raw3,raw4,b0_w12,raw1,raw2,raw0],[b0_w1,raw3,raw4,b0_w12,raw1,raw2,raw0],[b0_w2,raw3,raw1,b0_w12,raw4,raw2,raw0],[b0_w3,raw3,raw1,b0_w12,raw4,raw2,raw0],[b0_w4,raw3,raw2,b0_w12,raw4,raw1,raw0],[b0_w5,raw3,raw2,b0_w12,raw4,raw1,raw0],[b0_w6,raw3,raw0,b0_w12,raw4,raw1,raw2],[b0_w7,raw3,raw0,b0_w12,raw4,raw1,raw2],[b0_w8,raw4,raw1,b0_w12,raw3,raw2,raw0],[b0_w9,raw4,raw1,b0_w12,raw3,raw2,raw0],[b0_w10,raw4,raw2,b0_w12,raw3,raw1,raw0],[b0_w11,raw4,raw2,b0_w12,raw3,raw1,raw0],[b0_w13,raw0,b0_w12,raw3,raw1,raw2],[b0_w13,raw4,raw0,b0_w12,raw3,raw1,raw2],[b0_w14,raw1,raw2,b0_w12,raw3,raw4,raw0],[b0_w15,raw1,raw2,b0_w12,raw3,raw4,raw0],[b0_w16,raw1,raw0,b0_w12,raw3,raw4,raw2],[b0_w17,raw1,raw0,b0_w12,raw3,raw4,raw2],[b0_w18,raw2,raw0,b0_w12,raw3,raw4,raw1],[b0_w19,raw2,raw0,b0_w12,raw3,raw4,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead10
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead334
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead335
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead336
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead337
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead338
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead247
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead339
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead340
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead341
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead342
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead343
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead296
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead344
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead345
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead346
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead347
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead348
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead28
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead48
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead93
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead114
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead152
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead171
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead209
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead222
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead257
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead271
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead304
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead316
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead349
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead350
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead351
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead352
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead353
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead354
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead355
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead356
  · decide +kernel

def b0_s358 : List Sig := [b0_w77,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead358 : impossible 6 0 b0_s358 := by
  apply by_search
  decide +kernel

def b0_s359 : List Sig := [b0_w77,raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead359 : impossible 6 0 b0_s359 := by
  apply by_search
  decide +kernel

def b0_s360 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w13,b0_w31]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead360 : impossible 6 0 b0_s360 := by
  apply by_search
  decide +kernel

def b0_s361 : List Sig := [b0_w14,raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead361 : impossible 6 0 b0_s361 := by
  apply by_search
  decide +kernel

def b0_s362 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w15,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead362 : impossible 6 0 b0_s362 := by
  apply by_search
  decide +kernel

def b0_s363 : List Sig := [raw3,raw4,b0_w16,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead363 : impossible 6 0 b0_s363 := by
  apply by_search
  decide +kernel

def b0_s364 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w17,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead364 : impossible 6 0 b0_s364 := by
  apply by_search
  decide +kernel

def b0_s365 : List Sig := [raw3,raw4,b0_w78,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead365 : impossible 6 0 b0_s365 := by
  apply by_search
  decide +kernel

def b0_s366 : List Sig := [raw3,raw4,b0_w78,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead366 : impossible 6 0 b0_s366 := by
  apply by_search
  decide +kernel

def b0_s367 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w13,b0_w65]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead367 : impossible 6 0 b0_s367 := by
  apply by_search
  decide +kernel

def b0_s368 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead368 : impossible 6 0 b0_s368 := by
  apply by_search
  decide +kernel

def b0_s369 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w19,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead369 : impossible 6 0 b0_s369 := by
  apply by_search
  decide +kernel

def b0_s370 : List Sig := [raw3,raw4,raw1,b0_w79,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead370 : impossible 6 0 b0_s370 := by
  apply by_search
  decide +kernel

def b0_s371 : List Sig := [raw3,raw4,raw1,b0_w79,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead371 : impossible 6 0 b0_s371 := by
  apply by_search
  decide +kernel

def b0_s372 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w13,b0_w73]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead372 : impossible 6 0 b0_s372 := by
  apply by_search
  decide +kernel

def b0_s357 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead357 : impossible 7 0 b0_s357 := by
  apply reject_branch 6 0 b0_s357 [] [[b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w13],[b0_w1,raw3,raw1,raw2,raw0,b0_w13],[b0_w1,raw3,raw4,raw1,raw2,raw0,b0_w13],[b0_w2,raw3,raw1,raw4,raw2,raw0,b0_w13],[b0_w3,raw3,raw1,raw4,raw2,raw0,b0_w13],[b0_w4,raw3,raw2,raw4,raw1,raw0,b0_w13],[b0_w5,raw3,raw2,raw4,raw1,raw0,b0_w13],[b0_w6,raw3,raw0,raw4,raw1,raw2,b0_w13],[b0_w7,raw3,raw0,raw4,raw1,raw2,b0_w13],[b0_w77,raw3,raw4,raw1,raw2,raw0],[b0_w77,raw3,b0_w13,raw4,raw1,raw2,raw0],[b0_w31,raw3,raw4,raw1,raw2,raw0],[b0_w31,raw3,b0_w13,raw4,raw1,raw2,raw0],[b0_w8,raw4,raw1,raw3,raw2,raw0,b0_w13],[b0_w9,raw1,raw3,raw2,raw0,b0_w13],[b0_w9,raw4,raw1,raw3,raw2,raw0,b0_w13],[b0_w10,raw4,raw2,raw3,raw1,raw0,b0_w13],[b0_w11,raw2,raw3,raw1,raw0,b0_w13],[b0_w11,raw4,raw2,raw3,raw1,raw0,b0_w13],[b0_w12,raw0,raw3,raw1,raw2,b0_w13],[b0_w12,raw4,raw0,raw3,raw1,raw2,b0_w13],[b0_w14,raw1,raw2,raw3,raw4,raw0,b0_w13],[b0_w15,raw1,raw2,raw3,raw4,raw0,b0_w13],[b0_w16,raw1,raw0,raw3,raw4,raw2,b0_w13],[b0_w17,raw1,raw0,raw3,raw4,raw2,b0_w13],[b0_w78,raw1,raw3,raw4,raw2,raw0],[b0_w78,raw1,b0_w13,raw3,raw4,raw2,raw0],[b0_w65,raw1,raw3,raw4,raw2,raw0],[b0_w65,raw1,b0_w13,raw3,raw4,raw2,raw0],[b0_w18,raw2,raw0,raw3,raw4,raw1,b0_w13],[b0_w19,raw2,raw0,raw3,raw4,raw1,b0_w13],[b0_w79,raw2,raw3,raw4,raw1,raw0],[b0_w79,raw2,b0_w13,raw3,raw4,raw1,raw0],[b0_w73,raw2,raw3,raw4,raw1,raw0],[b0_w73,raw2,b0_w13,raw3,raw4,raw1,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead29
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead49
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead50
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead94
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead115
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead153
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead172
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead210
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead223
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead358
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead359
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead61
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead360
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead258
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead272
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead273
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead305
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead317
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead318
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead349
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead350
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead361
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead362
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead363
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead364
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead365
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead366
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead285
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead367
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead368
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead369
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead370
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead371
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead331
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead372
  · decide +kernel

def b0_s374 : List Sig := [b0_w33,b0_w14,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead374 : impossible 6 0 b0_s374 := by
  apply by_search
  decide +kernel

def b0_s375 : List Sig := [raw3,b0_w80,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead375 : impossible 6 0 b0_s375 := by
  apply by_search
  decide +kernel

def b0_s376 : List Sig := [b0_w14,raw3,b0_w80,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead376 : impossible 6 0 b0_s376 := by
  apply by_search
  decide +kernel

def b0_s377 : List Sig := [b0_w57,b0_w14,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead377 : impossible 6 0 b0_s377 := by
  apply by_search
  decide +kernel

def b0_s378 : List Sig := [raw3,raw4,b0_w81,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead378 : impossible 6 0 b0_s378 := by
  apply by_search
  decide +kernel

def b0_s379 : List Sig := [b0_w14,raw3,raw4,b0_w81,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead379 : impossible 6 0 b0_s379 := by
  apply by_search
  decide +kernel

def b0_s380 : List Sig := [b0_w82,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead380 : impossible 6 0 b0_s380 := by
  apply by_search
  decide +kernel

def b0_s381 : List Sig := [b0_w82,b0_w14,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead381 : impossible 6 0 b0_s381 := by
  apply by_search
  decide +kernel

def b0_s382 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w83]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead382 : impossible 6 0 b0_s382 := by
  apply by_search
  decide +kernel

def b0_s383 : List Sig := [b0_w14,raw3,raw4,raw1,raw2,raw0,b0_w83]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead383 : impossible 6 0 b0_s383 := by
  apply by_search
  decide +kernel

def b0_s384 : List Sig := [b0_w14,raw3,raw4,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead384 : impossible 6 0 b0_s384 := by
  apply by_search
  decide +kernel

def b0_s385 : List Sig := [b0_w14,raw3,raw4,raw1,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead385 : impossible 6 0 b0_s385 := by
  apply by_search
  decide +kernel

def b0_s386 : List Sig := [b0_w14,raw3,raw4,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead386 : impossible 6 0 b0_s386 := by
  apply by_search
  decide +kernel

def b0_s387 : List Sig := [b0_w14,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead387 : impossible 6 0 b0_s387 := by
  apply by_search
  decide +kernel

def b0_s388 : List Sig := [b0_w14,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead388 : impossible 6 0 b0_s388 := by
  apply by_search
  decide +kernel

def b0_s389 : List Sig := [b0_w14,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead389 : impossible 6 0 b0_s389 := by
  apply by_search
  decide +kernel

def b0_s390 : List Sig := [b0_w14,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead390 : impossible 6 0 b0_s390 := by
  apply by_search
  decide +kernel

def b0_s391 : List Sig := [b0_w14,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead391 : impossible 6 0 b0_s391 := by
  apply by_search
  decide +kernel

def b0_s373 : List Sig := [b0_w14,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead373 : impossible 7 0 b0_s373 := by
  apply reject_branch 6 0 b0_s373 [] [[b0_w33,raw3,raw4,raw1,raw2,raw0],[b0_w33,b0_w14,raw3,raw4,raw1,raw2,raw0],[b0_w80,raw3,raw4,raw1,raw2,raw0],[b0_w80,b0_w14,raw3,raw4,raw1,raw2,raw0],[b0_w57,raw4,raw3,raw1,raw2,raw0],[b0_w57,b0_w14,raw4,raw3,raw1,raw2,raw0],[b0_w81,raw4,raw3,raw1,raw2,raw0],[b0_w81,b0_w14,raw4,raw3,raw1,raw2,raw0],[b0_w82,raw0,raw3,raw4,raw1,raw2],[b0_w82,b0_w14,raw0,raw3,raw4,raw1,raw2],[b0_w83,raw0,raw3,raw4,raw1,raw2],[b0_w83,b0_w14,raw0,raw3,raw4,raw1,raw2],[b0_w0,raw3,raw4,b0_w14,raw1,raw2,raw0],[b0_w1,raw3,raw4,b0_w14,raw1,raw2,raw0],[b0_w2,raw3,raw1,b0_w14,raw4,raw2,raw0],[b0_w3,raw3,raw1,b0_w14,raw4,raw2,raw0],[b0_w4,raw3,raw2,b0_w14,raw4,raw1,raw0],[b0_w5,raw3,raw2,b0_w14,raw4,raw1,raw0],[b0_w6,raw3,raw0,b0_w14,raw4,raw1,raw2],[b0_w7,raw3,raw0,b0_w14,raw4,raw1,raw2],[b0_w8,raw4,raw1,b0_w14,raw3,raw2,raw0],[b0_w9,raw4,raw1,b0_w14,raw3,raw2,raw0],[b0_w10,raw4,raw2,b0_w14,raw3,raw1,raw0],[b0_w11,raw4,raw2,b0_w14,raw3,raw1,raw0],[b0_w12,raw4,raw0,b0_w14,raw3,raw1,raw2],[b0_w13,raw4,raw0,b0_w14,raw3,raw1,raw2],[b0_w15,b0_w14,raw3,raw4,raw0],[b0_w15,raw1,b0_w14,raw3,raw4,raw0],[b0_w15,raw2,b0_w14,raw3,raw4,raw0],[b0_w15,raw1,raw2,b0_w14,raw3,raw4,raw0],[b0_w16,raw1,raw0,b0_w14,raw3,raw4,raw2],[b0_w17,raw1,raw0,b0_w14,raw3,raw4,raw2],[b0_w18,raw2,raw0,b0_w14,raw3,raw4,raw1],[b0_w19,raw2,raw0,b0_w14,raw3,raw4,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead73
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead374
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead375
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead376
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead243
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead377
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead378
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead379
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead380
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead381
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead382
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead383
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead30
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead63
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead95
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead116
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead154
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead173
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead211
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead227
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead259
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead274
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead306
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead319
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead351
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead361
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead384
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead385
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead386
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead387
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead388
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead389
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead390
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead391
  · decide +kernel

def b0_s393 : List Sig := [b0_w84,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead393 : impossible 6 0 b0_s393 := by
  apply by_search
  decide +kernel

def b0_s394 : List Sig := [b0_w84,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead394 : impossible 6 0 b0_s394 := by
  apply by_search
  decide +kernel

def b0_s395 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w15,b0_w39]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead395 : impossible 6 0 b0_s395 := by
  apply by_search
  decide +kernel

def b0_s396 : List Sig := [b0_w85,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead396 : impossible 6 0 b0_s396 := by
  apply by_search
  decide +kernel

def b0_s397 : List Sig := [b0_w85,raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead397 : impossible 6 0 b0_s397 := by
  apply by_search
  decide +kernel

def b0_s398 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w15,b0_w63]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead398 : impossible 6 0 b0_s398 := by
  apply by_search
  decide +kernel

def b0_s399 : List Sig := [raw3,raw4,b0_w16,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead399 : impossible 6 0 b0_s399 := by
  apply by_search
  decide +kernel

def b0_s400 : List Sig := [raw3,raw4,raw2,raw0,b0_w17,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead400 : impossible 6 0 b0_s400 := by
  apply by_search
  decide +kernel

def b0_s401 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w17,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead401 : impossible 6 0 b0_s401 := by
  apply by_search
  decide +kernel

def b0_s402 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead402 : impossible 6 0 b0_s402 := by
  apply by_search
  decide +kernel

def b0_s403 : List Sig := [raw3,raw4,raw1,raw0,b0_w19,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead403 : impossible 6 0 b0_s403 := by
  apply by_search
  decide +kernel

def b0_s404 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w19,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead404 : impossible 6 0 b0_s404 := by
  apply by_search
  decide +kernel

def b0_s405 : List Sig := [raw3,raw4,raw1,raw2,b0_w86,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead405 : impossible 6 0 b0_s405 := by
  apply by_search
  decide +kernel

def b0_s406 : List Sig := [raw3,raw4,raw1,raw2,b0_w86,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead406 : impossible 6 0 b0_s406 := by
  apply by_search
  decide +kernel

def b0_s407 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w87]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead407 : impossible 6 0 b0_s407 := by
  apply by_search
  decide +kernel

def b0_s408 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w15,b0_w87]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead408 : impossible 6 0 b0_s408 := by
  apply by_search
  decide +kernel

def b0_s392 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead392 : impossible 7 0 b0_s392 := by
  apply reject_branch 6 0 b0_s392 [] [[b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w15],[b0_w1,raw3,raw4,raw1,raw2,raw0,b0_w15],[b0_w2,raw3,raw1,raw4,raw2,raw0,b0_w15],[b0_w3,raw3,raw1,raw4,raw2,raw0,b0_w15],[b0_w4,raw3,raw2,raw4,raw1,raw0,b0_w15],[b0_w5,raw3,raw2,raw4,raw1,raw0,b0_w15],[b0_w6,raw3,raw0,raw4,raw1,raw2,b0_w15],[b0_w7,raw3,raw0,raw4,raw1,raw2,b0_w15],[b0_w84,raw3,raw4,raw1,raw2,raw0],[b0_w84,raw3,b0_w15,raw4,raw1,raw2,raw0],[b0_w39,raw3,raw4,raw1,raw2,raw0],[b0_w39,raw3,b0_w15,raw4,raw1,raw2,raw0],[b0_w8,raw4,raw1,raw3,raw2,raw0,b0_w15],[b0_w9,raw4,raw1,raw3,raw2,raw0,b0_w15],[b0_w10,raw4,raw2,raw3,raw1,raw0,b0_w15],[b0_w11,raw4,raw2,raw3,raw1,raw0,b0_w15],[b0_w12,raw4,raw0,raw3,raw1,raw2,b0_w15],[b0_w13,raw4,raw0,raw3,raw1,raw2,b0_w15],[b0_w85,raw4,raw3,raw1,raw2,raw0],[b0_w85,raw4,b0_w15,raw3,raw1,raw2,raw0],[b0_w63,raw4,raw3,raw1,raw2,raw0],[b0_w63,raw4,b0_w15,raw3,raw1,raw2,raw0],[b0_w14,raw3,raw4,raw0,b0_w15],[b0_w14,raw1,raw3,raw4,raw0,b0_w15],[b0_w14,raw2,raw3,raw4,raw0,b0_w15],[b0_w14,raw1,raw2,raw3,raw4,raw0,b0_w15],[b0_w16,raw1,raw0,raw3,raw4,raw2,b0_w15],[b0_w17,raw0,raw3,raw4,raw2,b0_w15],[b0_w17,raw1,raw0,raw3,raw4,raw2,b0_w15],[b0_w18,raw2,raw0,raw3,raw4,raw1,b0_w15],[b0_w19,raw0,raw3,raw4,raw1,b0_w15],[b0_w19,raw2,raw0,raw3,raw4,raw1,b0_w15],[b0_w86,raw0,raw3,raw4,raw1,raw2],[b0_w86,raw0,b0_w15,raw3,raw4,raw1,raw2],[b0_w87,raw0,raw3,raw4,raw1,raw2],[b0_w87,raw0,b0_w15,raw3,raw4,raw1,raw2]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead31
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead64
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead96
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead117
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead155
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead174
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead212
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead228
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead393
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead394
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead123
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead395
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead260
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead275
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead307
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead320
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead352
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead362
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead396
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead397
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead281
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead398
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead384
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead385
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead386
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead387
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead399
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead400
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead401
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead402
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead403
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead404
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead405
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead406
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead407
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead408
  · decide +kernel

def b0_s410 : List Sig := [b0_w35,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead410 : impossible 6 0 b0_s410 := by
  apply by_search
  decide +kernel

def b0_s411 : List Sig := [raw4,raw1,b0_w88,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead411 : impossible 6 0 b0_s411 := by
  apply by_search
  decide +kernel

def b0_s412 : List Sig := [raw3,raw4,raw1,b0_w88,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead412 : impossible 6 0 b0_s412 := by
  apply by_search
  decide +kernel

def b0_s413 : List Sig := [raw4,b0_w16,raw1,b0_w88,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead413 : impossible 6 0 b0_s413 := by
  apply by_search
  decide +kernel

def b0_s414 : List Sig := [raw3,raw4,b0_w16,raw1,b0_w88,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead414 : impossible 6 0 b0_s414 := by
  apply by_search
  decide +kernel

def b0_s415 : List Sig := [b0_w59,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead415 : impossible 6 0 b0_s415 := by
  apply by_search
  decide +kernel

def b0_s416 : List Sig := [raw3,raw1,b0_w89,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead416 : impossible 6 0 b0_s416 := by
  apply by_search
  decide +kernel

def b0_s417 : List Sig := [raw3,raw4,raw1,b0_w89,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead417 : impossible 6 0 b0_s417 := by
  apply by_search
  decide +kernel

def b0_s418 : List Sig := [raw3,b0_w16,raw1,b0_w89,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead418 : impossible 6 0 b0_s418 := by
  apply by_search
  decide +kernel

def b0_s419 : List Sig := [raw3,raw4,b0_w16,raw1,b0_w89,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead419 : impossible 6 0 b0_s419 := by
  apply by_search
  decide +kernel

def b0_s420 : List Sig := [b0_w82,raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead420 : impossible 6 0 b0_s420 := by
  apply by_search
  decide +kernel

def b0_s421 : List Sig := [raw3,raw4,raw1,raw0,b0_w90]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead421 : impossible 6 0 b0_s421 := by
  apply by_search
  decide +kernel

def b0_s422 : List Sig := [raw3,raw4,b0_w16,raw1,raw0,b0_w90]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead422 : impossible 6 0 b0_s422 := by
  apply by_search
  decide +kernel

def b0_s423 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w90]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead423 : impossible 6 0 b0_s423 := by
  apply by_search
  decide +kernel

def b0_s424 : List Sig := [raw3,raw4,b0_w16,raw1,raw2,raw0,b0_w90]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead424 : impossible 6 0 b0_s424 := by
  apply by_search
  decide +kernel

def b0_s425 : List Sig := [raw3,raw4,b0_w16,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead425 : impossible 6 0 b0_s425 := by
  apply by_search
  decide +kernel

def b0_s426 : List Sig := [raw3,raw4,b0_w16,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead426 : impossible 6 0 b0_s426 := by
  apply by_search
  decide +kernel

def b0_s427 : List Sig := [raw3,raw4,b0_w16,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead427 : impossible 6 0 b0_s427 := by
  apply by_search
  decide +kernel

def b0_s428 : List Sig := [raw3,raw4,b0_w16,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead428 : impossible 6 0 b0_s428 := by
  apply by_search
  decide +kernel

def b0_s409 : List Sig := [raw3,raw4,b0_w16,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead409 : impossible 7 0 b0_s409 := by
  apply reject_branch 6 0 b0_s409 [] [[b0_w0,raw3,raw4,b0_w16,raw1,raw2,raw0],[b0_w1,raw3,raw4,b0_w16,raw1,raw2,raw0],[b0_w35,raw3,raw4,raw1,raw2,raw0],[b0_w35,raw3,b0_w16,raw4,raw1,raw2,raw0],[b0_w88,raw4,raw1,raw2,raw0],[b0_w88,raw3,raw4,raw1,raw2,raw0],[b0_w88,b0_w16,raw4,raw1,raw2,raw0],[b0_w88,raw3,b0_w16,raw4,raw1,raw2,raw0],[b0_w2,raw3,raw1,raw4,b0_w16,raw2,raw0],[b0_w3,raw3,raw1,raw4,b0_w16,raw2,raw0],[b0_w4,raw3,raw2,raw4,b0_w16,raw1,raw0],[b0_w5,raw3,raw2,raw4,b0_w16,raw1,raw0],[b0_w6,raw3,raw0,raw4,b0_w16,raw1,raw2],[b0_w7,raw3,raw0,raw4,b0_w16,raw1,raw2],[b0_w59,raw4,raw3,raw1,raw2,raw0],[b0_w59,raw4,b0_w16,raw3,raw1,raw2,raw0],[b0_w89,raw3,raw1,raw2,raw0],[b0_w89,raw4,raw3,raw1,raw2,raw0],[b0_w89,b0_w16,raw3,raw1,raw2,raw0],[b0_w89,raw4,b0_w16,raw3,raw1,raw2,raw0],[b0_w8,raw4,raw1,raw3,b0_w16,raw2,raw0],[b0_w9,raw4,raw1,raw3,b0_w16,raw2,raw0],[b0_w10,raw4,raw2,raw3,b0_w16,raw1,raw0],[b0_w11,raw4,raw2,raw3,b0_w16,raw1,raw0],[b0_w12,raw4,raw0,raw3,b0_w16,raw1,raw2],[b0_w13,raw4,raw0,raw3,b0_w16,raw1,raw2],[b0_w82,raw2,raw3,raw4,raw1,raw0],[b0_w82,b0_w16,raw2,raw3,raw4,raw1,raw0],[b0_w90,raw3,raw4,raw1,raw0],[b0_w90,b0_w16,raw3,raw4,raw1,raw0],[b0_w90,raw2,raw3,raw4,raw1,raw0],[b0_w90,b0_w16,raw2,raw3,raw4,raw1,raw0],[b0_w14,raw1,raw2,raw3,raw4,b0_w16,raw0],[b0_w15,raw1,raw2,raw3,raw4,b0_w16,raw0],[b0_w17,raw0,raw3,raw4,b0_w16,raw2],[b0_w17,raw1,raw0,raw3,raw4,b0_w16,raw2],[b0_w18,raw2,raw0,raw3,raw4,b0_w16,raw1],[b0_w19,raw2,raw0,raw3,raw4,b0_w16,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead32
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead65
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead77
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead410
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead411
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead412
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead413
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead414
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead97
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead118
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead156
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead178
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead213
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead229
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead247
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead415
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead416
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead417
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead418
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead419
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead261
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead276
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead308
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead324
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead353
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead363
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead380
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead420
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead421
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead422
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead423
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead424
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead388
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead399
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead425
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead426
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead427
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead428
  · decide +kernel

def b0_s430 : List Sig := [b0_w91,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead430 : impossible 6 0 b0_s430 := by
  apply by_search
  decide +kernel

def b0_s431 : List Sig := [b0_w91,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead431 : impossible 6 0 b0_s431 := by
  apply by_search
  decide +kernel

def b0_s432 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w17,b0_w41]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead432 : impossible 6 0 b0_s432 := by
  apply by_search
  decide +kernel

def b0_s433 : List Sig := [b0_w92,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead433 : impossible 6 0 b0_s433 := by
  apply by_search
  decide +kernel

def b0_s434 : List Sig := [b0_w92,raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead434 : impossible 6 0 b0_s434 := by
  apply by_search
  decide +kernel

def b0_s435 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w17,b0_w65]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead435 : impossible 6 0 b0_s435 := by
  apply by_search
  decide +kernel

def b0_s436 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead436 : impossible 6 0 b0_s436 := by
  apply by_search
  decide +kernel

def b0_s437 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w17,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead437 : impossible 6 0 b0_s437 := by
  apply by_search
  decide +kernel

def b0_s438 : List Sig := [raw3,raw4,raw1,b0_w93,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead438 : impossible 6 0 b0_s438 := by
  apply by_search
  decide +kernel

def b0_s439 : List Sig := [raw3,raw4,raw1,b0_w93,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead439 : impossible 6 0 b0_s439 := by
  apply by_search
  decide +kernel

def b0_s440 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w17,b0_w87]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead440 : impossible 6 0 b0_s440 := by
  apply by_search
  decide +kernel

def b0_s429 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead429 : impossible 7 0 b0_s429 := by
  apply reject_branch 6 0 b0_s429 [] [[b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w17],[b0_w1,raw3,raw4,raw1,raw2,raw0,b0_w17],[b0_w2,raw3,raw1,raw4,raw2,raw0,b0_w17],[b0_w3,raw3,raw4,raw2,raw0,b0_w17],[b0_w3,raw3,raw1,raw4,raw2,raw0,b0_w17],[b0_w4,raw3,raw2,raw4,raw1,raw0,b0_w17],[b0_w5,raw3,raw2,raw4,raw1,raw0,b0_w17],[b0_w6,raw3,raw0,raw4,raw1,raw2,b0_w17],[b0_w7,raw3,raw0,raw4,raw1,raw2,b0_w17],[b0_w91,raw3,raw4,raw1,raw2,raw0],[b0_w91,raw3,b0_w17,raw4,raw1,raw2,raw0],[b0_w41,raw3,raw4,raw1,raw2,raw0],[b0_w41,raw3,b0_w17,raw4,raw1,raw2,raw0],[b0_w8,raw4,raw1,raw3,raw2,raw0,b0_w17],[b0_w9,raw4,raw3,raw2,raw0,b0_w17],[b0_w9,raw4,raw1,raw3,raw2,raw0,b0_w17],[b0_w10,raw4,raw2,raw3,raw1,raw0,b0_w17],[b0_w11,raw4,raw2,raw3,raw1,raw0,b0_w17],[b0_w12,raw4,raw0,raw3,raw1,raw2,b0_w17],[b0_w13,raw4,raw0,raw3,raw1,raw2,b0_w17],[b0_w92,raw4,raw3,raw1,raw2,raw0],[b0_w92,raw4,b0_w17,raw3,raw1,raw2,raw0],[b0_w65,raw4,raw3,raw1,raw2,raw0],[b0_w65,raw4,b0_w17,raw3,raw1,raw2,raw0],[b0_w14,raw1,raw2,raw3,raw4,raw0,b0_w17],[b0_w15,raw2,raw3,raw4,raw0,b0_w17],[b0_w15,raw1,raw2,raw3,raw4,raw0,b0_w17],[b0_w16,raw0,raw3,raw4,raw2,b0_w17],[b0_w16,raw1,raw0,raw3,raw4,raw2,b0_w17],[b0_w18,raw2,raw0,raw3,raw4,raw1,b0_w17],[b0_w19,raw2,raw0,raw3,raw4,raw1,b0_w17],[b0_w93,raw2,raw3,raw4,raw1,raw0],[b0_w93,raw2,b0_w17,raw3,raw4,raw1,raw0],[b0_w87,raw2,raw3,raw4,raw1,raw0],[b0_w87,raw2,b0_w17,raw3,raw4,raw1,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead33
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead66
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead98
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead119
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead120
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead157
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead179
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead214
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead230
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead430
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead431
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead127
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead432
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead262
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead277
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead278
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead309
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead325
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead354
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead364
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead433
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead434
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead285
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead435
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead389
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead400
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead401
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead425
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead426
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead436
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead437
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead438
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead439
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead407
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead440
  · decide +kernel

def b0_s442 : List Sig := [b0_w44,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead442 : impossible 6 0 b0_s442 := by
  apply by_search
  decide +kernel

def b0_s443 : List Sig := [raw4,raw1,raw2,b0_w94,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead443 : impossible 6 0 b0_s443 := by
  apply by_search
  decide +kernel

def b0_s444 : List Sig := [raw3,raw4,raw1,raw2,b0_w94,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead444 : impossible 6 0 b0_s444 := by
  apply by_search
  decide +kernel

def b0_s445 : List Sig := [raw4,raw1,b0_w18,raw2,b0_w94,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead445 : impossible 6 0 b0_s445 := by
  apply by_search
  decide +kernel

def b0_s446 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,b0_w94,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead446 : impossible 6 0 b0_s446 := by
  apply by_search
  decide +kernel

def b0_s447 : List Sig := [b0_w68,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead447 : impossible 6 0 b0_s447 := by
  apply by_search
  decide +kernel

def b0_s448 : List Sig := [raw3,raw1,raw2,b0_w95,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead448 : impossible 6 0 b0_s448 := by
  apply by_search
  decide +kernel

def b0_s449 : List Sig := [raw3,raw4,raw1,raw2,b0_w95,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead449 : impossible 6 0 b0_s449 := by
  apply by_search
  decide +kernel

def b0_s450 : List Sig := [raw3,raw1,b0_w18,raw2,b0_w95,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead450 : impossible 6 0 b0_s450 := by
  apply by_search
  decide +kernel

def b0_s451 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,b0_w95,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead451 : impossible 6 0 b0_s451 := by
  apply by_search
  decide +kernel

def b0_s452 : List Sig := [b0_w82,raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead452 : impossible 6 0 b0_s452 := by
  apply by_search
  decide +kernel

def b0_s453 : List Sig := [raw3,raw4,raw2,raw0,b0_w96]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead453 : impossible 6 0 b0_s453 := by
  apply by_search
  decide +kernel

def b0_s454 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w96]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead454 : impossible 6 0 b0_s454 := by
  apply by_search
  decide +kernel

def b0_s455 : List Sig := [raw3,raw4,b0_w18,raw2,raw0,b0_w96]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead455 : impossible 6 0 b0_s455 := by
  apply by_search
  decide +kernel

def b0_s456 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,raw0,b0_w96]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead456 : impossible 6 0 b0_s456 := by
  apply by_search
  decide +kernel

def b0_s457 : List Sig := [raw3,raw4,raw1,b0_w18,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead457 : impossible 6 0 b0_s457 := by
  apply by_search
  decide +kernel

def b0_s458 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead458 : impossible 6 0 b0_s458 := by
  apply by_search
  decide +kernel

def b0_s441 : List Sig := [raw3,raw4,raw1,b0_w18,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead441 : impossible 7 0 b0_s441 := by
  apply reject_branch 6 0 b0_s441 [] [[b0_w0,raw3,raw4,raw1,b0_w18,raw2,raw0],[b0_w1,raw3,raw4,raw1,b0_w18,raw2,raw0],[b0_w2,raw3,raw1,raw4,b0_w18,raw2,raw0],[b0_w3,raw3,raw1,raw4,b0_w18,raw2,raw0],[b0_w44,raw3,raw4,raw1,raw2,raw0],[b0_w44,raw3,b0_w18,raw4,raw1,raw2,raw0],[b0_w94,raw4,raw1,raw2,raw0],[b0_w94,raw3,raw4,raw1,raw2,raw0],[b0_w94,b0_w18,raw4,raw1,raw2,raw0],[b0_w94,raw3,b0_w18,raw4,raw1,raw2,raw0],[b0_w4,raw3,raw2,raw4,raw1,b0_w18,raw0],[b0_w5,raw3,raw2,raw4,raw1,b0_w18,raw0],[b0_w6,raw3,raw0,raw4,raw1,b0_w18,raw2],[b0_w7,raw3,raw0,raw4,raw1,b0_w18,raw2],[b0_w8,raw4,raw1,raw3,b0_w18,raw2,raw0],[b0_w9,raw4,raw1,raw3,b0_w18,raw2,raw0],[b0_w68,raw4,raw3,raw1,raw2,raw0],[b0_w68,raw4,b0_w18,raw3,raw1,raw2,raw0],[b0_w95,raw3,raw1,raw2,raw0],[b0_w95,raw4,raw3,raw1,raw2,raw0],[b0_w95,b0_w18,raw3,raw1,raw2,raw0],[b0_w95,raw4,b0_w18,raw3,raw1,raw2,raw0],[b0_w10,raw4,raw2,raw3,raw1,b0_w18,raw0],[b0_w11,raw4,raw2,raw3,raw1,b0_w18,raw0],[b0_w12,raw4,raw0,raw3,raw1,b0_w18,raw2],[b0_w13,raw4,raw0,raw3,raw1,b0_w18,raw2],[b0_w82,raw1,raw3,raw4,raw2,raw0],[b0_w82,raw1,b0_w18,raw3,raw4,raw2,raw0],[b0_w96,raw3,raw4,raw2,raw0],[b0_w96,raw1,raw3,raw4,raw2,raw0],[b0_w96,b0_w18,raw3,raw4,raw2,raw0],[b0_w96,raw1,b0_w18,raw3,raw4,raw2,raw0],[b0_w14,raw1,raw2,raw3,raw4,b0_w18,raw0],[b0_w15,raw1,raw2,raw3,raw4,b0_w18,raw0],[b0_w16,raw1,raw0,raw3,raw4,b0_w18,raw2],[b0_w17,raw1,raw0,raw3,raw4,b0_w18,raw2],[b0_w19,raw0,raw3,raw4,raw1,b0_w18],[b0_w19,raw2,raw0,raw3,raw4,raw1,b0_w18]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead34
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead67
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead99
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead129
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead138
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead442
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead443
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead444
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead445
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead446
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead158
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead180
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead215
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead234
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead263
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead287
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead296
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead447
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead448
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead449
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead450
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead451
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead310
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead326
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead355
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead368
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead380
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead452
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead453
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead454
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead455
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead456
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead390
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead402
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead427
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead436
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead457
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead458
  · decide +kernel

def b0_s460 : List Sig := [b0_w97,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead460 : impossible 6 0 b0_s460 := by
  apply by_search
  decide +kernel

def b0_s461 : List Sig := [b0_w97,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead461 : impossible 6 0 b0_s461 := by
  apply by_search
  decide +kernel

def b0_s462 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w19,b0_w49]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead462 : impossible 6 0 b0_s462 := by
  apply by_search
  decide +kernel

def b0_s463 : List Sig := [b0_w98,raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead463 : impossible 6 0 b0_s463 := by
  apply by_search
  decide +kernel

def b0_s464 : List Sig := [b0_w98,raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead464 : impossible 6 0 b0_s464 := by
  apply by_search
  decide +kernel

def b0_s465 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w19,b0_w73]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead465 : impossible 6 0 b0_s465 := by
  apply by_search
  decide +kernel

def b0_s466 : List Sig := [raw3,raw4,b0_w99,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead466 : impossible 6 0 b0_s466 := by
  apply by_search
  decide +kernel

def b0_s467 : List Sig := [raw3,raw4,b0_w99,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead467 : impossible 6 0 b0_s467 := by
  apply by_search
  decide +kernel

def b0_s468 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w19,b0_w87]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead468 : impossible 6 0 b0_s468 := by
  apply by_search
  decide +kernel

def b0_s459 : List Sig := [raw3,raw4,raw1,raw2,raw0,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead459 : impossible 7 0 b0_s459 := by
  apply reject_branch 6 0 b0_s459 [] [[b0_w0,raw3,raw4,raw1,raw2,raw0,b0_w19],[b0_w1,raw3,raw4,raw1,raw2,raw0,b0_w19],[b0_w2,raw3,raw1,raw4,raw2,raw0,b0_w19],[b0_w3,raw3,raw1,raw4,raw2,raw0,b0_w19],[b0_w4,raw3,raw2,raw4,raw1,raw0,b0_w19],[b0_w5,raw3,raw4,raw1,raw0,b0_w19],[b0_w5,raw3,raw2,raw4,raw1,raw0,b0_w19],[b0_w6,raw3,raw0,raw4,raw1,raw2,b0_w19],[b0_w7,raw3,raw0,raw4,raw1,raw2,b0_w19],[b0_w97,raw3,raw4,raw1,raw2,raw0],[b0_w97,raw3,b0_w19,raw4,raw1,raw2,raw0],[b0_w49,raw3,raw4,raw1,raw2,raw0],[b0_w49,raw3,b0_w19,raw4,raw1,raw2,raw0],[b0_w8,raw4,raw1,raw3,raw2,raw0,b0_w19],[b0_w9,raw4,raw1,raw3,raw2,raw0,b0_w19],[b0_w10,raw4,raw2,raw3,raw1,raw0,b0_w19],[b0_w11,raw4,raw3,raw1,raw0,b0_w19],[b0_w11,raw4,raw2,raw3,raw1,raw0,b0_w19],[b0_w12,raw4,raw0,raw3,raw1,raw2,b0_w19],[b0_w13,raw4,raw0,raw3,raw1,raw2,b0_w19],[b0_w98,raw4,raw3,raw1,raw2,raw0],[b0_w98,raw4,b0_w19,raw3,raw1,raw2,raw0],[b0_w73,raw4,raw3,raw1,raw2,raw0],[b0_w73,raw4,b0_w19,raw3,raw1,raw2,raw0],[b0_w14,raw1,raw2,raw3,raw4,raw0,b0_w19],[b0_w15,raw1,raw3,raw4,raw0,b0_w19],[b0_w15,raw1,raw2,raw3,raw4,raw0,b0_w19],[b0_w16,raw1,raw0,raw3,raw4,raw2,b0_w19],[b0_w17,raw1,raw0,raw3,raw4,raw2,b0_w19],[b0_w99,raw1,raw3,raw4,raw2,raw0],[b0_w99,raw1,b0_w19,raw3,raw4,raw2,raw0],[b0_w87,raw1,raw3,raw4,raw2,raw0],[b0_w87,raw1,b0_w19,raw3,raw4,raw2,raw0],[b0_w18,raw0,raw3,raw4,raw1,b0_w19],[b0_w18,raw2,raw0,raw3,raw4,raw1,b0_w19]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead35
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead68
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead100
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead130
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead159
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead181
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead182
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead216
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead235
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead460
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead461
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead185
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead462
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead264
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead288
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead311
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead327
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead328
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead356
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead369
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead463
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead464
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead331
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead465
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead391
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead403
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead404
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead428
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead437
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead466
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead467
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead407
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead468
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead457
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead458
  · decide +kernel

def b0_s0 : List Sig := [raw3,raw4,raw1,raw2,raw0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead0 : impossible 8 0 b0_s0 := by
  apply reject_branch 7 0 b0_s0 [] [[b0_w0,raw3,raw4,raw1,raw2,raw0],[b0_w1,raw3,raw4,raw1,raw2,raw0],[b0_w2,raw3,raw1,raw4,raw2,raw0],[b0_w3,raw3,raw1,raw4,raw2,raw0],[b0_w4,raw3,raw2,raw4,raw1,raw0],[b0_w5,raw3,raw2,raw4,raw1,raw0],[b0_w6,raw3,raw0,raw4,raw1,raw2],[b0_w7,raw3,raw0,raw4,raw1,raw2],[b0_w8,raw4,raw1,raw3,raw2,raw0],[b0_w9,raw4,raw1,raw3,raw2,raw0],[b0_w10,raw4,raw2,raw3,raw1,raw0],[b0_w11,raw4,raw2,raw3,raw1,raw0],[b0_w12,raw4,raw0,raw3,raw1,raw2],[b0_w13,raw4,raw0,raw3,raw1,raw2],[b0_w14,raw1,raw2,raw3,raw4,raw0],[b0_w15,raw1,raw2,raw3,raw4,raw0],[b0_w16,raw1,raw0,raw3,raw4,raw2],[b0_w17,raw1,raw0,raw3,raw4,raw2],[b0_w18,raw2,raw0,raw3,raw4,raw1],[b0_w19,raw2,raw0,raw3,raw4,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead1
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead36
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead69
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead101
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead131
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead160
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead187
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead217
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead239
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead265
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead289
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead312
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead333
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead357
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead373
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead392
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead409
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead429
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead441
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead459
  · decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem branch_exclude_0 : impossible 8 0 raw :=
  impossible_same (by decide +kernel) (by decide +kernel) b0_dead0

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    9 ≤ C.size := by
  by_contra! hc
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length = 5 := rfl
  change C.gates.length < 9 at hc
  have hk8 : k ≤ 8 := by omega
  have ht4 : t ≤ 4 := by omega
  have no : impossible 8 t raw := by
    interval_cases t
    · exact branch_exclude_0
    · exact by_search exclude_1
    · exact by_search exclude_2
    · exact by_search exclude_3
    · exact by_search exclude_4
  exact no ht hk8 raw_nd eq

def upperGates : List Gate := [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.or, [12, 10]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 9 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 13⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case7

namespace Case8

def raw0 : Sig := (0xffffff000fff000fff000ffffff000ffffffffffff000ffffffffffff000fff,0x2012012012012012012012012012012012012012012012012012012012012012)
def raw1 : Sig := (0xffffffffff000000ffffff000ffffff000fff000ffffff000fff000fffffffff,0x4244244244244244244244244244244244244244244244244244244244244244)
def raw2 : Sig := (0xf000ffffffffffff000000000fffffffff000000fffffffff000000ffffff000,0x8498498498498498498498498498498498498498498498498498498498498498)
def raw3 : Sig := (0xfffffffffffffffffffff000000000000000fffffffffffffff000000000,0x8e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e0)
def raw4 : Sig := (0xffffffffffffffffffffffffffffffffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfeeaeac8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 8)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 4, search 8 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 8 at hc
  exact ⟨t,by omega,search_complete ht 8 (by omega) raw raw_nd eq⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_1 : search 8 1 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_2 : search 8 2 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_3 : search 8 3 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_4 : search 8 4 raw = false := by decide +kernel

def b0_w0 : Sig := bin false raw3 raw4
def b0_w1 : Sig := bin true raw3 raw4
def b0_w2 : Sig := bin false raw3 raw0
def b0_w3 : Sig := bin true raw3 raw0
def b0_w4 : Sig := bin false raw3 raw2
def b0_w5 : Sig := bin true raw3 raw2
def b0_w6 : Sig := bin false raw3 raw1
def b0_w7 : Sig := bin true raw3 raw1
def b0_w8 : Sig := bin false raw4 raw0
def b0_w9 : Sig := bin true raw4 raw0
def b0_w10 : Sig := bin false raw4 raw2
def b0_w11 : Sig := bin true raw4 raw2
def b0_w12 : Sig := bin false raw4 raw1
def b0_w13 : Sig := bin true raw4 raw1
def b0_w14 : Sig := bin false raw0 raw2
def b0_w15 : Sig := bin true raw0 raw2
def b0_w16 : Sig := bin false raw0 raw1
def b0_w17 : Sig := bin true raw0 raw1
def b0_w18 : Sig := bin false raw2 raw1
def b0_w19 : Sig := bin true raw2 raw1
def b0_w20 : Sig := bin false b0_w0 raw0
def b0_w21 : Sig := bin true b0_w0 raw0
def b0_w22 : Sig := bin false b0_w0 raw2
def b0_w23 : Sig := bin true b0_w0 raw2
def b0_w24 : Sig := bin false b0_w0 raw1
def b0_w25 : Sig := bin true b0_w0 raw1
def b0_w26 : Sig := bin false b0_w1 raw0
def b0_w27 : Sig := bin true b0_w1 raw0
def b0_w28 : Sig := bin false b0_w1 raw2
def b0_w29 : Sig := bin true b0_w1 raw2
def b0_w30 : Sig := bin false b0_w1 raw1
def b0_w31 : Sig := bin true b0_w1 raw1
def b0_w32 : Sig := bin true b0_w2 raw4
def b0_w33 : Sig := bin false b0_w2 raw2
def b0_w34 : Sig := bin true b0_w2 raw2
def b0_w35 : Sig := bin false b0_w2 raw1
def b0_w36 : Sig := bin true b0_w2 raw1
def b0_w37 : Sig := bin false raw4 b0_w3
def b0_w38 : Sig := bin false b0_w3 raw2
def b0_w39 : Sig := bin true b0_w3 raw2
def b0_w40 : Sig := bin false b0_w3 raw1
def b0_w41 : Sig := bin true b0_w3 raw1
def b0_w42 : Sig := bin true b0_w4 raw4
def b0_w43 : Sig := bin true b0_w4 raw0
def b0_w44 : Sig := bin false b0_w4 raw1
def b0_w45 : Sig := bin true b0_w4 raw1
def b0_w46 : Sig := bin false raw4 b0_w5
def b0_w47 : Sig := bin false raw0 b0_w5
def b0_w48 : Sig := bin false b0_w5 raw1
def b0_w49 : Sig := bin true b0_w5 raw1
def b0_w50 : Sig := bin true b0_w6 raw4
def b0_w51 : Sig := bin true b0_w6 raw0
def b0_w52 : Sig := bin true b0_w6 raw2
def b0_w53 : Sig := bin false raw4 b0_w7
def b0_w54 : Sig := bin false raw0 b0_w7
def b0_w55 : Sig := bin false raw2 b0_w7
def b0_w56 : Sig := bin true b0_w8 raw3
def b0_w57 : Sig := bin false b0_w8 raw2
def b0_w58 : Sig := bin true b0_w8 raw2
def b0_w59 : Sig := bin false b0_w8 raw1
def b0_w60 : Sig := bin true b0_w8 raw1
def b0_w61 : Sig := bin false raw3 b0_w9
def b0_w62 : Sig := bin false b0_w9 raw2
def b0_w63 : Sig := bin true b0_w9 raw2
def b0_w64 : Sig := bin false b0_w9 raw1
def b0_w65 : Sig := bin true b0_w9 raw1
def b0_w66 : Sig := bin true b0_w10 raw3
def b0_w67 : Sig := bin true b0_w10 raw0
def b0_w68 : Sig := bin false b0_w10 raw1
def b0_w69 : Sig := bin true b0_w10 raw1
def b0_w70 : Sig := bin false raw3 b0_w11
def b0_w71 : Sig := bin false raw0 b0_w11
def b0_w72 : Sig := bin false b0_w11 raw1
def b0_w73 : Sig := bin true b0_w11 raw1
def b0_w74 : Sig := bin true b0_w12 raw3
def b0_w75 : Sig := bin true b0_w12 raw0
def b0_w76 : Sig := bin true b0_w12 raw2
def b0_w77 : Sig := bin false raw3 b0_w13
def b0_w78 : Sig := bin false raw0 b0_w13
def b0_w79 : Sig := bin false raw2 b0_w13
def b0_w80 : Sig := bin true b0_w14 raw3
def b0_w81 : Sig := bin true b0_w14 raw4
def b0_w82 : Sig := bin false b0_w14 raw1
def b0_w83 : Sig := bin true b0_w14 raw1
def b0_w84 : Sig := bin false raw3 b0_w15
def b0_w85 : Sig := bin false raw4 b0_w15
def b0_w86 : Sig := bin false raw1 b0_w15
def b0_w87 : Sig := bin true raw1 b0_w15
def b0_w88 : Sig := bin true raw3 b0_w16
def b0_w89 : Sig := bin true raw4 b0_w16
def b0_w90 : Sig := bin true b0_w16 raw2
def b0_w91 : Sig := bin false raw3 b0_w17
def b0_w92 : Sig := bin false raw4 b0_w17
def b0_w93 : Sig := bin false raw2 b0_w17
def b0_w94 : Sig := bin true raw3 b0_w18
def b0_w95 : Sig := bin true raw4 b0_w18
def b0_w96 : Sig := bin true raw0 b0_w18
def b0_w97 : Sig := bin false raw3 b0_w19
def b0_w98 : Sig := bin false raw4 b0_w19
def b0_w99 : Sig := bin false raw0 b0_w19

def b0_s2 : List Sig := [b0_w20,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead2 : impossible 6 0 b0_s2 := by
  apply by_search
  decide +kernel

def b0_s3 : List Sig := [b0_w20,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead3 : impossible 6 0 b0_s3 := by
  apply by_search
  decide +kernel

def b0_s4 : List Sig := [raw3,raw4,raw0,b0_w21,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead4 : impossible 6 0 b0_s4 := by
  apply by_search
  decide +kernel

def b0_s5 : List Sig := [b0_w0,raw3,raw4,raw0,b0_w21,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead5 : impossible 6 0 b0_s5 := by
  apply by_search
  decide +kernel

def b0_s6 : List Sig := [b0_w22,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead6 : impossible 6 0 b0_s6 := by
  apply by_search
  decide +kernel

def b0_s7 : List Sig := [b0_w22,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead7 : impossible 6 0 b0_s7 := by
  apply by_search
  decide +kernel

def b0_s8 : List Sig := [raw3,raw4,raw0,raw2,b0_w23,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead8 : impossible 6 0 b0_s8 := by
  apply by_search
  decide +kernel

def b0_s9 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,b0_w23,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead9 : impossible 6 0 b0_s9 := by
  apply by_search
  decide +kernel

def b0_s10 : List Sig := [b0_w24,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead10 : impossible 6 0 b0_s10 := by
  apply by_search
  decide +kernel

def b0_s11 : List Sig := [b0_w24,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead11 : impossible 6 0 b0_s11 := by
  apply by_search
  decide +kernel

def b0_s12 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w25]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead12 : impossible 6 0 b0_s12 := by
  apply by_search
  decide +kernel

def b0_s13 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w25]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead13 : impossible 6 0 b0_s13 := by
  apply by_search
  decide +kernel

def b0_s14 : List Sig := [b0_w0,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead14 : impossible 6 0 b0_s14 := by
  apply by_search
  decide +kernel

def b0_s15 : List Sig := [b0_w0,raw3,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead15 : impossible 6 0 b0_s15 := by
  apply by_search
  decide +kernel

def b0_s16 : List Sig := [b0_w0,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead16 : impossible 6 0 b0_s16 := by
  apply by_search
  decide +kernel

def b0_s17 : List Sig := [b0_w0,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead17 : impossible 6 0 b0_s17 := by
  apply by_search
  decide +kernel

def b0_s18 : List Sig := [b0_w2,b0_w0,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead18 : impossible 6 0 b0_s18 := by
  apply by_search
  decide +kernel

def b0_s19 : List Sig := [b0_w2,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead19 : impossible 6 0 b0_s19 := by
  apply by_search
  decide +kernel

def b0_s20 : List Sig := [b0_w0,raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead20 : impossible 6 0 b0_s20 := by
  apply by_search
  decide +kernel

def b0_s21 : List Sig := [b0_w4,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead21 : impossible 6 0 b0_s21 := by
  apply by_search
  decide +kernel

def b0_s22 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead22 : impossible 6 0 b0_s22 := by
  apply by_search
  decide +kernel

def b0_s23 : List Sig := [b0_w6,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead23 : impossible 6 0 b0_s23 := by
  apply by_search
  decide +kernel

def b0_s24 : List Sig := [b0_w0,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead24 : impossible 6 0 b0_s24 := by
  apply by_search
  decide +kernel

def b0_s25 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead25 : impossible 6 0 b0_s25 := by
  apply by_search
  decide +kernel

def b0_s26 : List Sig := [b0_w8,b0_w0,raw3,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead26 : impossible 6 0 b0_s26 := by
  apply by_search
  decide +kernel

def b0_s27 : List Sig := [b0_w8,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead27 : impossible 6 0 b0_s27 := by
  apply by_search
  decide +kernel

def b0_s28 : List Sig := [b0_w0,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead28 : impossible 6 0 b0_s28 := by
  apply by_search
  decide +kernel

def b0_s29 : List Sig := [b0_w10,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead29 : impossible 6 0 b0_s29 := by
  apply by_search
  decide +kernel

def b0_s30 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead30 : impossible 6 0 b0_s30 := by
  apply by_search
  decide +kernel

def b0_s31 : List Sig := [b0_w12,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead31 : impossible 6 0 b0_s31 := by
  apply by_search
  decide +kernel

def b0_s32 : List Sig := [b0_w0,raw3,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead32 : impossible 6 0 b0_s32 := by
  apply by_search
  decide +kernel

def b0_s33 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead33 : impossible 6 0 b0_s33 := by
  apply by_search
  decide +kernel

def b0_s34 : List Sig := [b0_w14,b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead34 : impossible 6 0 b0_s34 := by
  apply by_search
  decide +kernel

def b0_s35 : List Sig := [b0_w0,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead35 : impossible 6 0 b0_s35 := by
  apply by_search
  decide +kernel

def b0_s36 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead36 : impossible 6 0 b0_s36 := by
  apply by_search
  decide +kernel

def b0_s37 : List Sig := [b0_w0,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead37 : impossible 6 0 b0_s37 := by
  apply by_search
  decide +kernel

def b0_s38 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead38 : impossible 6 0 b0_s38 := by
  apply by_search
  decide +kernel

def b0_s39 : List Sig := [b0_w0,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead39 : impossible 6 0 b0_s39 := by
  apply by_search
  decide +kernel

def b0_s40 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead40 : impossible 6 0 b0_s40 := by
  apply by_search
  decide +kernel

def b0_s1 : List Sig := [b0_w0,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead1 : impossible 7 0 b0_s1 := by
  apply reject_branch 6 0 b0_s1 [] [[b0_w20,raw0,raw3,raw4,raw2,raw1],[b0_w20,b0_w0,raw0,raw3,raw4,raw2,raw1],[b0_w21,raw0,raw3,raw4,raw2,raw1],[b0_w21,b0_w0,raw0,raw3,raw4,raw2,raw1],[b0_w22,raw2,raw3,raw4,raw0,raw1],[b0_w22,b0_w0,raw2,raw3,raw4,raw0,raw1],[b0_w23,raw2,raw3,raw4,raw0,raw1],[b0_w23,b0_w0,raw2,raw3,raw4,raw0,raw1],[b0_w24,raw1,raw3,raw4,raw0,raw2],[b0_w24,b0_w0,raw1,raw3,raw4,raw0,raw2],[b0_w25,raw1,raw3,raw4,raw0,raw2],[b0_w25,b0_w0,raw1,raw3,raw4,raw0,raw2],[b0_w1,b0_w0,raw0,raw2,raw1],[b0_w1,raw3,b0_w0,raw0,raw2,raw1],[b0_w1,raw4,b0_w0,raw0,raw2,raw1],[b0_w1,raw3,raw4,b0_w0,raw0,raw2,raw1],[b0_w2,raw0,b0_w0,raw4,raw2,raw1],[b0_w2,raw3,raw0,b0_w0,raw4,raw2,raw1],[b0_w3,raw3,raw0,b0_w0,raw4,raw2,raw1],[b0_w4,raw3,raw2,b0_w0,raw4,raw0,raw1],[b0_w5,raw3,raw2,b0_w0,raw4,raw0,raw1],[b0_w6,raw3,raw1,b0_w0,raw4,raw0,raw2],[b0_w7,raw1,b0_w0,raw4,raw0,raw2],[b0_w7,raw3,raw1,b0_w0,raw4,raw0,raw2],[b0_w8,raw0,b0_w0,raw3,raw2,raw1],[b0_w8,raw4,raw0,b0_w0,raw3,raw2,raw1],[b0_w9,raw4,raw0,b0_w0,raw3,raw2,raw1],[b0_w10,raw4,raw2,b0_w0,raw3,raw0,raw1],[b0_w11,raw4,raw2,b0_w0,raw3,raw0,raw1],[b0_w12,raw4,raw1,b0_w0,raw3,raw0,raw2],[b0_w13,raw1,b0_w0,raw3,raw0,raw2],[b0_w13,raw4,raw1,b0_w0,raw3,raw0,raw2],[b0_w14,raw0,raw2,b0_w0,raw3,raw4,raw1],[b0_w15,raw0,b0_w0,raw3,raw4,raw1],[b0_w15,raw0,raw2,b0_w0,raw3,raw4,raw1],[b0_w16,raw0,raw1,b0_w0,raw3,raw4,raw2],[b0_w17,raw0,raw1,b0_w0,raw3,raw4,raw2],[b0_w18,raw2,raw1,b0_w0,raw3,raw4,raw0],[b0_w19,raw2,raw1,b0_w0,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead2
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead3
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead4
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead5
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead6
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead7
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead8
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead9
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead10
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead11
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead12
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead13
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead14
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead15
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead16
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead17
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead18
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead19
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead20
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead21
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead22
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead23
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead24
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead25
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead26
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead27
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead28
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead29
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead30
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead31
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead32
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead33
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead34
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead35
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead36
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead37
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead38
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead39
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead40
  · decide +kernel

def b0_s42 : List Sig := [b0_w2,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead42 : impossible 6 0 b0_s42 := by
  apply by_search
  decide +kernel

def b0_s43 : List Sig := [raw4,b0_w1,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead43 : impossible 6 0 b0_s43 := by
  apply by_search
  decide +kernel

def b0_s44 : List Sig := [raw3,raw4,b0_w1,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead44 : impossible 6 0 b0_s44 := by
  apply by_search
  decide +kernel

def b0_s45 : List Sig := [b0_w4,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead45 : impossible 6 0 b0_s45 := by
  apply by_search
  decide +kernel

def b0_s46 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead46 : impossible 6 0 b0_s46 := by
  apply by_search
  decide +kernel

def b0_s47 : List Sig := [b0_w6,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead47 : impossible 6 0 b0_s47 := by
  apply by_search
  decide +kernel

def b0_s48 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead48 : impossible 6 0 b0_s48 := by
  apply by_search
  decide +kernel

def b0_s49 : List Sig := [b0_w8,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead49 : impossible 6 0 b0_s49 := by
  apply by_search
  decide +kernel

def b0_s50 : List Sig := [raw3,b0_w1,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead50 : impossible 6 0 b0_s50 := by
  apply by_search
  decide +kernel

def b0_s51 : List Sig := [raw3,raw4,b0_w1,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead51 : impossible 6 0 b0_s51 := by
  apply by_search
  decide +kernel

def b0_s52 : List Sig := [b0_w10,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead52 : impossible 6 0 b0_s52 := by
  apply by_search
  decide +kernel

def b0_s53 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead53 : impossible 6 0 b0_s53 := by
  apply by_search
  decide +kernel

def b0_s54 : List Sig := [b0_w12,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead54 : impossible 6 0 b0_s54 := by
  apply by_search
  decide +kernel

def b0_s55 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead55 : impossible 6 0 b0_s55 := by
  apply by_search
  decide +kernel

def b0_s56 : List Sig := [b0_w26,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead56 : impossible 6 0 b0_s56 := by
  apply by_search
  decide +kernel

def b0_s57 : List Sig := [b0_w26,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead57 : impossible 6 0 b0_s57 := by
  apply by_search
  decide +kernel

def b0_s58 : List Sig := [raw3,raw4,raw0,b0_w27,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead58 : impossible 6 0 b0_s58 := by
  apply by_search
  decide +kernel

def b0_s59 : List Sig := [raw3,raw4,b0_w1,raw0,b0_w27,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead59 : impossible 6 0 b0_s59 := by
  apply by_search
  decide +kernel

def b0_s60 : List Sig := [b0_w28,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead60 : impossible 6 0 b0_s60 := by
  apply by_search
  decide +kernel

def b0_s61 : List Sig := [b0_w28,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead61 : impossible 6 0 b0_s61 := by
  apply by_search
  decide +kernel

def b0_s62 : List Sig := [raw3,raw4,raw0,raw2,b0_w29,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead62 : impossible 6 0 b0_s62 := by
  apply by_search
  decide +kernel

def b0_s63 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,b0_w29,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead63 : impossible 6 0 b0_s63 := by
  apply by_search
  decide +kernel

def b0_s64 : List Sig := [b0_w30,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead64 : impossible 6 0 b0_s64 := by
  apply by_search
  decide +kernel

def b0_s65 : List Sig := [b0_w30,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead65 : impossible 6 0 b0_s65 := by
  apply by_search
  decide +kernel

def b0_s66 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w31]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead66 : impossible 6 0 b0_s66 := by
  apply by_search
  decide +kernel

def b0_s67 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,raw1,b0_w31]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead67 : impossible 6 0 b0_s67 := by
  apply by_search
  decide +kernel

def b0_s68 : List Sig := [b0_w14,raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead68 : impossible 6 0 b0_s68 := by
  apply by_search
  decide +kernel

def b0_s69 : List Sig := [raw3,raw4,b0_w1,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead69 : impossible 6 0 b0_s69 := by
  apply by_search
  decide +kernel

def b0_s70 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead70 : impossible 6 0 b0_s70 := by
  apply by_search
  decide +kernel

def b0_s71 : List Sig := [raw3,raw4,b0_w1,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead71 : impossible 6 0 b0_s71 := by
  apply by_search
  decide +kernel

def b0_s72 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead72 : impossible 6 0 b0_s72 := by
  apply by_search
  decide +kernel

def b0_s73 : List Sig := [raw3,raw4,b0_w1,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead73 : impossible 6 0 b0_s73 := by
  apply by_search
  decide +kernel

def b0_s74 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead74 : impossible 6 0 b0_s74 := by
  apply by_search
  decide +kernel

def b0_s41 : List Sig := [raw3,raw4,b0_w1,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead41 : impossible 7 0 b0_s41 := by
  apply reject_branch 6 0 b0_s41 [] [[b0_w0,b0_w1,raw0,raw2,raw1],[b0_w0,raw3,b0_w1,raw0,raw2,raw1],[b0_w0,raw4,b0_w1,raw0,raw2,raw1],[b0_w0,raw3,raw4,b0_w1,raw0,raw2,raw1],[b0_w2,raw3,raw0,raw4,b0_w1,raw2,raw1],[b0_w3,raw0,raw4,b0_w1,raw2,raw1],[b0_w3,raw3,raw0,raw4,b0_w1,raw2,raw1],[b0_w4,raw3,raw2,raw4,b0_w1,raw0,raw1],[b0_w5,raw3,raw2,raw4,b0_w1,raw0,raw1],[b0_w6,raw3,raw1,raw4,b0_w1,raw0,raw2],[b0_w7,raw3,raw1,raw4,b0_w1,raw0,raw2],[b0_w8,raw4,raw0,raw3,b0_w1,raw2,raw1],[b0_w9,raw0,raw3,b0_w1,raw2,raw1],[b0_w9,raw4,raw0,raw3,b0_w1,raw2,raw1],[b0_w10,raw4,raw2,raw3,b0_w1,raw0,raw1],[b0_w11,raw4,raw2,raw3,b0_w1,raw0,raw1],[b0_w12,raw4,raw1,raw3,b0_w1,raw0,raw2],[b0_w13,raw4,raw1,raw3,b0_w1,raw0,raw2],[b0_w26,raw0,raw3,raw4,raw2,raw1],[b0_w26,b0_w1,raw0,raw3,raw4,raw2,raw1],[b0_w27,raw0,raw3,raw4,raw2,raw1],[b0_w27,b0_w1,raw0,raw3,raw4,raw2,raw1],[b0_w28,raw2,raw3,raw4,raw0,raw1],[b0_w28,b0_w1,raw2,raw3,raw4,raw0,raw1],[b0_w29,raw2,raw3,raw4,raw0,raw1],[b0_w29,b0_w1,raw2,raw3,raw4,raw0,raw1],[b0_w30,raw1,raw3,raw4,raw0,raw2],[b0_w30,b0_w1,raw1,raw3,raw4,raw0,raw2],[b0_w31,raw1,raw3,raw4,raw0,raw2],[b0_w31,b0_w1,raw1,raw3,raw4,raw0,raw2],[b0_w14,raw0,raw2,raw3,raw4,b0_w1,raw1],[b0_w15,raw0,raw3,raw4,b0_w1,raw1],[b0_w15,raw0,raw2,raw3,raw4,b0_w1,raw1],[b0_w16,raw0,raw1,raw3,raw4,b0_w1,raw2],[b0_w17,raw0,raw1,raw3,raw4,b0_w1,raw2],[b0_w18,raw2,raw1,raw3,raw4,b0_w1,raw0],[b0_w19,raw2,raw1,raw3,raw4,b0_w1,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead14
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead15
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead16
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead17
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead42
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead43
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead44
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead45
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead46
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead47
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead48
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead49
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead50
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead51
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead52
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead53
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead54
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead55
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead56
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead57
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead58
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead59
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead60
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead61
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead62
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead63
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead64
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead65
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead66
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead67
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead68
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead69
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead70
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead71
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead72
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead73
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead74
  · decide +kernel

def b0_s76 : List Sig := [b0_w20,b0_w2,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead76 : impossible 6 0 b0_s76 := by
  apply by_search
  decide +kernel

def b0_s77 : List Sig := [raw3,b0_w32,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead77 : impossible 6 0 b0_s77 := by
  apply by_search
  decide +kernel

def b0_s78 : List Sig := [b0_w2,raw3,b0_w32,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead78 : impossible 6 0 b0_s78 := by
  apply by_search
  decide +kernel

def b0_s79 : List Sig := [raw3,raw4,b0_w32,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead79 : impossible 6 0 b0_s79 := by
  apply by_search
  decide +kernel

def b0_s80 : List Sig := [b0_w2,raw3,raw4,b0_w32,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead80 : impossible 6 0 b0_s80 := by
  apply by_search
  decide +kernel

def b0_s81 : List Sig := [b0_w33,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead81 : impossible 6 0 b0_s81 := by
  apply by_search
  decide +kernel

def b0_s82 : List Sig := [b0_w33,b0_w2,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead82 : impossible 6 0 b0_s82 := by
  apply by_search
  decide +kernel

def b0_s83 : List Sig := [raw3,raw4,raw0,b0_w34,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead83 : impossible 6 0 b0_s83 := by
  apply by_search
  decide +kernel

def b0_s84 : List Sig := [b0_w2,raw3,raw4,raw0,b0_w34,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead84 : impossible 6 0 b0_s84 := by
  apply by_search
  decide +kernel

def b0_s85 : List Sig := [raw3,raw4,raw0,raw2,b0_w34,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead85 : impossible 6 0 b0_s85 := by
  apply by_search
  decide +kernel

def b0_s86 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,b0_w34,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead86 : impossible 6 0 b0_s86 := by
  apply by_search
  decide +kernel

def b0_s87 : List Sig := [b0_w35,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead87 : impossible 6 0 b0_s87 := by
  apply by_search
  decide +kernel

def b0_s88 : List Sig := [b0_w35,b0_w2,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead88 : impossible 6 0 b0_s88 := by
  apply by_search
  decide +kernel

def b0_s89 : List Sig := [raw3,raw4,raw0,raw2,b0_w36]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead89 : impossible 6 0 b0_s89 := by
  apply by_search
  decide +kernel

def b0_s90 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,b0_w36]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead90 : impossible 6 0 b0_s90 := by
  apply by_search
  decide +kernel

def b0_s91 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w36]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead91 : impossible 6 0 b0_s91 := by
  apply by_search
  decide +kernel

def b0_s92 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,raw1,b0_w36]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead92 : impossible 6 0 b0_s92 := by
  apply by_search
  decide +kernel

def b0_s93 : List Sig := [b0_w2,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead93 : impossible 6 0 b0_s93 := by
  apply by_search
  decide +kernel

def b0_s94 : List Sig := [b0_w2,raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead94 : impossible 6 0 b0_s94 := by
  apply by_search
  decide +kernel

def b0_s95 : List Sig := [b0_w2,b0_w4,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead95 : impossible 6 0 b0_s95 := by
  apply by_search
  decide +kernel

def b0_s96 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead96 : impossible 6 0 b0_s96 := by
  apply by_search
  decide +kernel

def b0_s97 : List Sig := [b0_w2,b0_w6,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead97 : impossible 6 0 b0_s97 := by
  apply by_search
  decide +kernel

def b0_s98 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead98 : impossible 6 0 b0_s98 := by
  apply by_search
  decide +kernel

def b0_s99 : List Sig := [b0_w2,b0_w8,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead99 : impossible 6 0 b0_s99 := by
  apply by_search
  decide +kernel

def b0_s100 : List Sig := [b0_w2,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead100 : impossible 6 0 b0_s100 := by
  apply by_search
  decide +kernel

def b0_s101 : List Sig := [b0_w2,b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead101 : impossible 6 0 b0_s101 := by
  apply by_search
  decide +kernel

def b0_s102 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead102 : impossible 6 0 b0_s102 := by
  apply by_search
  decide +kernel

def b0_s103 : List Sig := [b0_w2,b0_w12,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead103 : impossible 6 0 b0_s103 := by
  apply by_search
  decide +kernel

def b0_s104 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead104 : impossible 6 0 b0_s104 := by
  apply by_search
  decide +kernel

def b0_s105 : List Sig := [b0_w14,b0_w2,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead105 : impossible 6 0 b0_s105 := by
  apply by_search
  decide +kernel

def b0_s106 : List Sig := [b0_w2,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead106 : impossible 6 0 b0_s106 := by
  apply by_search
  decide +kernel

def b0_s107 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead107 : impossible 6 0 b0_s107 := by
  apply by_search
  decide +kernel

def b0_s108 : List Sig := [b0_w2,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead108 : impossible 6 0 b0_s108 := by
  apply by_search
  decide +kernel

def b0_s109 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead109 : impossible 6 0 b0_s109 := by
  apply by_search
  decide +kernel

def b0_s110 : List Sig := [b0_w2,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead110 : impossible 6 0 b0_s110 := by
  apply by_search
  decide +kernel

def b0_s111 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead111 : impossible 6 0 b0_s111 := by
  apply by_search
  decide +kernel

def b0_s75 : List Sig := [b0_w2,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead75 : impossible 7 0 b0_s75 := by
  apply reject_branch 6 0 b0_s75 [] [[b0_w20,raw4,raw3,raw0,raw2,raw1],[b0_w20,b0_w2,raw4,raw3,raw0,raw2,raw1],[b0_w32,raw3,raw0,raw2,raw1],[b0_w32,b0_w2,raw3,raw0,raw2,raw1],[b0_w32,raw4,raw3,raw0,raw2,raw1],[b0_w32,b0_w2,raw4,raw3,raw0,raw2,raw1],[b0_w33,raw2,raw3,raw4,raw0,raw1],[b0_w33,b0_w2,raw2,raw3,raw4,raw0,raw1],[b0_w34,raw3,raw4,raw0,raw1],[b0_w34,b0_w2,raw3,raw4,raw0,raw1],[b0_w34,raw2,raw3,raw4,raw0,raw1],[b0_w34,b0_w2,raw2,raw3,raw4,raw0,raw1],[b0_w35,raw1,raw3,raw4,raw0,raw2],[b0_w35,b0_w2,raw1,raw3,raw4,raw0,raw2],[b0_w36,raw3,raw4,raw0,raw2],[b0_w36,b0_w2,raw3,raw4,raw0,raw2],[b0_w36,raw1,raw3,raw4,raw0,raw2],[b0_w36,b0_w2,raw1,raw3,raw4,raw0,raw2],[b0_w0,raw4,b0_w2,raw0,raw2,raw1],[b0_w0,raw3,raw4,b0_w2,raw0,raw2,raw1],[b0_w1,raw3,raw4,b0_w2,raw0,raw2,raw1],[b0_w3,raw0,b0_w2,raw4,raw2,raw1],[b0_w3,raw3,raw0,b0_w2,raw4,raw2,raw1],[b0_w4,raw3,raw2,b0_w2,raw4,raw0,raw1],[b0_w5,raw3,raw2,b0_w2,raw4,raw0,raw1],[b0_w6,raw3,raw1,b0_w2,raw4,raw0,raw2],[b0_w7,raw3,raw1,b0_w2,raw4,raw0,raw2],[b0_w8,raw4,raw0,b0_w2,raw3,raw2,raw1],[b0_w9,raw4,raw0,b0_w2,raw3,raw2,raw1],[b0_w10,raw4,raw2,b0_w2,raw3,raw0,raw1],[b0_w11,raw4,raw2,b0_w2,raw3,raw0,raw1],[b0_w12,raw4,raw1,b0_w2,raw3,raw0,raw2],[b0_w13,raw4,raw1,b0_w2,raw3,raw0,raw2],[b0_w14,raw0,raw2,b0_w2,raw3,raw4,raw1],[b0_w15,raw0,b0_w2,raw3,raw4,raw1],[b0_w15,raw0,raw2,b0_w2,raw3,raw4,raw1],[b0_w16,raw0,raw1,b0_w2,raw3,raw4,raw2],[b0_w17,raw0,raw1,b0_w2,raw3,raw4,raw2],[b0_w18,raw2,raw1,b0_w2,raw3,raw4,raw0],[b0_w19,raw2,raw1,b0_w2,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead2
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead76
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead77
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead78
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead79
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead80
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead81
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead82
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead83
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead84
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead85
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead86
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead87
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead88
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead89
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead90
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead91
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead92
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead18
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead19
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead42
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead93
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead94
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead95
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead96
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead97
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead98
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead99
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead100
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead101
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead102
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead103
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead104
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead105
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead106
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead107
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead108
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead109
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead110
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead111
  · decide +kernel

def b0_s113 : List Sig := [b0_w4,raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead113 : impossible 6 0 b0_s113 := by
  apply by_search
  decide +kernel

def b0_s114 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead114 : impossible 6 0 b0_s114 := by
  apply by_search
  decide +kernel

def b0_s115 : List Sig := [b0_w6,raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead115 : impossible 6 0 b0_s115 := by
  apply by_search
  decide +kernel

def b0_s116 : List Sig := [raw4,raw0,b0_w3,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead116 : impossible 6 0 b0_s116 := by
  apply by_search
  decide +kernel

def b0_s117 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead117 : impossible 6 0 b0_s117 := by
  apply by_search
  decide +kernel

def b0_s118 : List Sig := [b0_w8,raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead118 : impossible 6 0 b0_s118 := by
  apply by_search
  decide +kernel

def b0_s119 : List Sig := [raw3,raw4,raw0,b0_w3,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead119 : impossible 6 0 b0_s119 := by
  apply by_search
  decide +kernel

def b0_s120 : List Sig := [raw3,b0_w37,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead120 : impossible 6 0 b0_s120 := by
  apply by_search
  decide +kernel

def b0_s121 : List Sig := [raw3,b0_w37,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead121 : impossible 6 0 b0_s121 := by
  apply by_search
  decide +kernel

def b0_s122 : List Sig := [raw3,b0_w37,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead122 : impossible 6 0 b0_s122 := by
  apply by_search
  decide +kernel

def b0_s123 : List Sig := [raw3,b0_w37,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead123 : impossible 6 0 b0_s123 := by
  apply by_search
  decide +kernel

def b0_s124 : List Sig := [raw3,raw4,raw0,b0_w3,b0_w27,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead124 : impossible 6 0 b0_s124 := by
  apply by_search
  decide +kernel

def b0_s125 : List Sig := [b0_w10,raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead125 : impossible 6 0 b0_s125 := by
  apply by_search
  decide +kernel

def b0_s126 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead126 : impossible 6 0 b0_s126 := by
  apply by_search
  decide +kernel

def b0_s127 : List Sig := [b0_w12,raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead127 : impossible 6 0 b0_s127 := by
  apply by_search
  decide +kernel

def b0_s128 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead128 : impossible 6 0 b0_s128 := by
  apply by_search
  decide +kernel

def b0_s129 : List Sig := [b0_w14,raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead129 : impossible 6 0 b0_s129 := by
  apply by_search
  decide +kernel

def b0_s130 : List Sig := [raw3,raw4,raw0,b0_w3,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead130 : impossible 6 0 b0_s130 := by
  apply by_search
  decide +kernel

def b0_s131 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead131 : impossible 6 0 b0_s131 := by
  apply by_search
  decide +kernel

def b0_s132 : List Sig := [raw3,raw4,b0_w16,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead132 : impossible 6 0 b0_s132 := by
  apply by_search
  decide +kernel

def b0_s133 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead133 : impossible 6 0 b0_s133 := by
  apply by_search
  decide +kernel

def b0_s134 : List Sig := [b0_w38,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead134 : impossible 6 0 b0_s134 := by
  apply by_search
  decide +kernel

def b0_s135 : List Sig := [b0_w38,raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead135 : impossible 6 0 b0_s135 := by
  apply by_search
  decide +kernel

def b0_s136 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w39]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead136 : impossible 6 0 b0_s136 := by
  apply by_search
  decide +kernel

def b0_s137 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,raw1,b0_w39]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead137 : impossible 6 0 b0_s137 := by
  apply by_search
  decide +kernel

def b0_s138 : List Sig := [raw3,raw4,raw0,b0_w40,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead138 : impossible 6 0 b0_s138 := by
  apply by_search
  decide +kernel

def b0_s139 : List Sig := [raw3,raw4,raw0,b0_w40,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead139 : impossible 6 0 b0_s139 := by
  apply by_search
  decide +kernel

def b0_s140 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w41]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead140 : impossible 6 0 b0_s140 := by
  apply by_search
  decide +kernel

def b0_s141 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,raw1,b0_w41]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead141 : impossible 6 0 b0_s141 := by
  apply by_search
  decide +kernel

def b0_s142 : List Sig := [raw3,raw4,raw0,b0_w3,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead142 : impossible 6 0 b0_s142 := by
  apply by_search
  decide +kernel

def b0_s143 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead143 : impossible 6 0 b0_s143 := by
  apply by_search
  decide +kernel

def b0_s112 : List Sig := [raw3,raw4,raw0,b0_w3,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead112 : impossible 7 0 b0_s112 := by
  apply reject_branch 6 0 b0_s112 [] [[b0_w0,raw3,raw4,raw0,b0_w3,raw2,raw1],[b0_w1,raw4,raw0,b0_w3,raw2,raw1],[b0_w1,raw3,raw4,raw0,b0_w3,raw2,raw1],[b0_w2,raw0,raw4,b0_w3,raw2,raw1],[b0_w2,raw3,raw0,raw4,b0_w3,raw2,raw1],[b0_w4,raw3,raw2,raw4,raw0,b0_w3,raw1],[b0_w5,raw3,raw2,raw4,raw0,b0_w3,raw1],[b0_w6,raw3,raw1,raw4,raw0,b0_w3,raw2],[b0_w7,raw1,raw4,raw0,b0_w3,raw2],[b0_w7,raw3,raw1,raw4,raw0,b0_w3,raw2],[b0_w8,raw4,raw0,raw3,b0_w3,raw2,raw1],[b0_w9,raw4,raw0,raw3,b0_w3,raw2,raw1],[b0_w37,raw3,raw0,raw2,raw1],[b0_w37,raw4,raw3,raw0,raw2,raw1],[b0_w37,b0_w3,raw3,raw0,raw2,raw1],[b0_w37,raw4,b0_w3,raw3,raw0,raw2,raw1],[b0_w27,raw4,raw3,raw0,raw2,raw1],[b0_w27,raw4,b0_w3,raw3,raw0,raw2,raw1],[b0_w10,raw4,raw2,raw3,raw0,b0_w3,raw1],[b0_w11,raw4,raw2,raw3,raw0,b0_w3,raw1],[b0_w12,raw4,raw1,raw3,raw0,b0_w3,raw2],[b0_w13,raw4,raw1,raw3,raw0,b0_w3,raw2],[b0_w14,raw0,raw2,raw3,raw4,b0_w3,raw1],[b0_w15,raw0,raw3,raw4,b0_w3,raw1],[b0_w15,raw0,raw2,raw3,raw4,b0_w3,raw1],[b0_w16,raw0,raw1,raw3,raw4,b0_w3,raw2],[b0_w17,raw0,raw1,raw3,raw4,b0_w3,raw2],[b0_w38,raw2,raw3,raw4,raw0,raw1],[b0_w38,b0_w3,raw2,raw3,raw4,raw0,raw1],[b0_w39,raw2,raw3,raw4,raw0,raw1],[b0_w39,b0_w3,raw2,raw3,raw4,raw0,raw1],[b0_w40,raw1,raw3,raw4,raw0,raw2],[b0_w40,b0_w3,raw1,raw3,raw4,raw0,raw2],[b0_w41,raw1,raw3,raw4,raw0,raw2],[b0_w41,b0_w3,raw1,raw3,raw4,raw0,raw2],[b0_w18,raw2,raw1,raw3,raw4,raw0,b0_w3],[b0_w19,raw2,raw1,raw3,raw4,raw0,b0_w3]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead20
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead43
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead44
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead93
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead94
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead113
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead114
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead115
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead116
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead117
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead118
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead119
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead120
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead121
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead122
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead123
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead58
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead124
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead125
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead126
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead127
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead128
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead129
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead130
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead131
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead132
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead133
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead134
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead135
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead136
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead137
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead138
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead139
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead140
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead141
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead142
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead143
  · decide +kernel

def b0_s145 : List Sig := [b0_w22,b0_w4,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead145 : impossible 6 0 b0_s145 := by
  apply by_search
  decide +kernel

def b0_s146 : List Sig := [raw3,raw4,b0_w42,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead146 : impossible 6 0 b0_s146 := by
  apply by_search
  decide +kernel

def b0_s147 : List Sig := [b0_w4,raw3,raw4,b0_w42,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead147 : impossible 6 0 b0_s147 := by
  apply by_search
  decide +kernel

def b0_s148 : List Sig := [b0_w33,b0_w4,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead148 : impossible 6 0 b0_s148 := by
  apply by_search
  decide +kernel

def b0_s149 : List Sig := [raw3,raw4,raw0,b0_w43,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead149 : impossible 6 0 b0_s149 := by
  apply by_search
  decide +kernel

def b0_s150 : List Sig := [b0_w4,raw3,raw4,raw0,b0_w43,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead150 : impossible 6 0 b0_s150 := by
  apply by_search
  decide +kernel

def b0_s151 : List Sig := [b0_w44,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead151 : impossible 6 0 b0_s151 := by
  apply by_search
  decide +kernel

def b0_s152 : List Sig := [b0_w44,b0_w4,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead152 : impossible 6 0 b0_s152 := by
  apply by_search
  decide +kernel

def b0_s153 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w45]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead153 : impossible 6 0 b0_s153 := by
  apply by_search
  decide +kernel

def b0_s154 : List Sig := [b0_w4,raw3,raw4,raw0,raw2,raw1,b0_w45]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead154 : impossible 6 0 b0_s154 := by
  apply by_search
  decide +kernel

def b0_s155 : List Sig := [b0_w4,raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead155 : impossible 6 0 b0_s155 := by
  apply by_search
  decide +kernel

def b0_s156 : List Sig := [b0_w6,b0_w4,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead156 : impossible 6 0 b0_s156 := by
  apply by_search
  decide +kernel

def b0_s157 : List Sig := [b0_w4,raw3,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead157 : impossible 6 0 b0_s157 := by
  apply by_search
  decide +kernel

def b0_s158 : List Sig := [b0_w8,b0_w4,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead158 : impossible 6 0 b0_s158 := by
  apply by_search
  decide +kernel

def b0_s159 : List Sig := [b0_w4,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead159 : impossible 6 0 b0_s159 := by
  apply by_search
  decide +kernel

def b0_s160 : List Sig := [b0_w4,b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead160 : impossible 6 0 b0_s160 := by
  apply by_search
  decide +kernel

def b0_s161 : List Sig := [b0_w4,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead161 : impossible 6 0 b0_s161 := by
  apply by_search
  decide +kernel

def b0_s162 : List Sig := [b0_w12,b0_w4,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead162 : impossible 6 0 b0_s162 := by
  apply by_search
  decide +kernel

def b0_s163 : List Sig := [b0_w4,raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead163 : impossible 6 0 b0_s163 := by
  apply by_search
  decide +kernel

def b0_s164 : List Sig := [b0_w14,b0_w4,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead164 : impossible 6 0 b0_s164 := by
  apply by_search
  decide +kernel

def b0_s165 : List Sig := [b0_w4,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead165 : impossible 6 0 b0_s165 := by
  apply by_search
  decide +kernel

def b0_s166 : List Sig := [b0_w4,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead166 : impossible 6 0 b0_s166 := by
  apply by_search
  decide +kernel

def b0_s167 : List Sig := [b0_w4,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead167 : impossible 6 0 b0_s167 := by
  apply by_search
  decide +kernel

def b0_s168 : List Sig := [b0_w4,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead168 : impossible 6 0 b0_s168 := by
  apply by_search
  decide +kernel

def b0_s169 : List Sig := [b0_w4,raw3,raw4,raw0,b0_w18,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead169 : impossible 6 0 b0_s169 := by
  apply by_search
  decide +kernel

def b0_s170 : List Sig := [b0_w4,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead170 : impossible 6 0 b0_s170 := by
  apply by_search
  decide +kernel

def b0_s171 : List Sig := [b0_w4,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead171 : impossible 6 0 b0_s171 := by
  apply by_search
  decide +kernel

def b0_s144 : List Sig := [b0_w4,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead144 : impossible 7 0 b0_s144 := by
  apply reject_branch 6 0 b0_s144 [] [[b0_w22,raw4,raw3,raw0,raw2,raw1],[b0_w22,b0_w4,raw4,raw3,raw0,raw2,raw1],[b0_w42,raw4,raw3,raw0,raw2,raw1],[b0_w42,b0_w4,raw4,raw3,raw0,raw2,raw1],[b0_w33,raw0,raw3,raw4,raw2,raw1],[b0_w33,b0_w4,raw0,raw3,raw4,raw2,raw1],[b0_w43,raw0,raw3,raw4,raw2,raw1],[b0_w43,b0_w4,raw0,raw3,raw4,raw2,raw1],[b0_w44,raw1,raw3,raw4,raw0,raw2],[b0_w44,b0_w4,raw1,raw3,raw4,raw0,raw2],[b0_w45,raw1,raw3,raw4,raw0,raw2],[b0_w45,b0_w4,raw1,raw3,raw4,raw0,raw2],[b0_w0,raw3,raw4,b0_w4,raw0,raw2,raw1],[b0_w1,raw3,raw4,b0_w4,raw0,raw2,raw1],[b0_w2,raw3,raw0,b0_w4,raw4,raw2,raw1],[b0_w3,raw3,raw0,b0_w4,raw4,raw2,raw1],[b0_w5,raw3,raw2,b0_w4,raw4,raw0,raw1],[b0_w6,raw3,raw1,b0_w4,raw4,raw0,raw2],[b0_w7,raw3,raw1,b0_w4,raw4,raw0,raw2],[b0_w8,raw4,raw0,b0_w4,raw3,raw2,raw1],[b0_w9,raw4,raw0,b0_w4,raw3,raw2,raw1],[b0_w10,raw4,raw2,b0_w4,raw3,raw0,raw1],[b0_w11,raw4,raw2,b0_w4,raw3,raw0,raw1],[b0_w12,raw4,raw1,b0_w4,raw3,raw0,raw2],[b0_w13,raw4,raw1,b0_w4,raw3,raw0,raw2],[b0_w14,raw0,raw2,b0_w4,raw3,raw4,raw1],[b0_w15,raw0,b0_w4,raw3,raw4,raw1],[b0_w15,raw0,raw2,b0_w4,raw3,raw4,raw1],[b0_w16,raw0,raw1,b0_w4,raw3,raw4,raw2],[b0_w17,raw0,raw1,b0_w4,raw3,raw4,raw2],[b0_w18,raw1,b0_w4,raw3,raw4,raw0],[b0_w18,raw2,raw1,b0_w4,raw3,raw4,raw0],[b0_w19,raw2,raw1,b0_w4,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead6
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead145
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead146
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead147
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead81
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead148
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead149
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead150
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead151
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead152
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead153
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead154
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead21
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead45
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead95
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead113
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead155
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead156
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead157
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead158
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead159
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead160
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead161
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead162
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead163
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead164
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead165
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead166
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead167
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead168
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead169
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead170
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead171
  · decide +kernel

def b0_s173 : List Sig := [b0_w6,raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead173 : impossible 6 0 b0_s173 := by
  apply by_search
  decide +kernel

def b0_s174 : List Sig := [raw4,raw0,raw2,b0_w5,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead174 : impossible 6 0 b0_s174 := by
  apply by_search
  decide +kernel

def b0_s175 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead175 : impossible 6 0 b0_s175 := by
  apply by_search
  decide +kernel

def b0_s176 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead176 : impossible 6 0 b0_s176 := by
  apply by_search
  decide +kernel

def b0_s177 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead177 : impossible 6 0 b0_s177 := by
  apply by_search
  decide +kernel

def b0_s178 : List Sig := [b0_w10,raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead178 : impossible 6 0 b0_s178 := by
  apply by_search
  decide +kernel

def b0_s179 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead179 : impossible 6 0 b0_s179 := by
  apply by_search
  decide +kernel

def b0_s180 : List Sig := [raw3,b0_w46,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead180 : impossible 6 0 b0_s180 := by
  apply by_search
  decide +kernel

def b0_s181 : List Sig := [raw3,b0_w46,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead181 : impossible 6 0 b0_s181 := by
  apply by_search
  decide +kernel

def b0_s182 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,b0_w29,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead182 : impossible 6 0 b0_s182 := by
  apply by_search
  decide +kernel

def b0_s183 : List Sig := [b0_w12,raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead183 : impossible 6 0 b0_s183 := by
  apply by_search
  decide +kernel

def b0_s184 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead184 : impossible 6 0 b0_s184 := by
  apply by_search
  decide +kernel

def b0_s185 : List Sig := [b0_w14,raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead185 : impossible 6 0 b0_s185 := by
  apply by_search
  decide +kernel

def b0_s186 : List Sig := [raw3,raw4,raw0,b0_w5,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead186 : impossible 6 0 b0_s186 := by
  apply by_search
  decide +kernel

def b0_s187 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead187 : impossible 6 0 b0_s187 := by
  apply by_search
  decide +kernel

def b0_s188 : List Sig := [b0_w47,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead188 : impossible 6 0 b0_s188 := by
  apply by_search
  decide +kernel

def b0_s189 : List Sig := [b0_w47,raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead189 : impossible 6 0 b0_s189 := by
  apply by_search
  decide +kernel

def b0_s190 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,raw1,b0_w39]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead190 : impossible 6 0 b0_s190 := by
  apply by_search
  decide +kernel

def b0_s191 : List Sig := [raw3,raw4,b0_w16,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead191 : impossible 6 0 b0_s191 := by
  apply by_search
  decide +kernel

def b0_s192 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead192 : impossible 6 0 b0_s192 := by
  apply by_search
  decide +kernel

def b0_s193 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead193 : impossible 6 0 b0_s193 := by
  apply by_search
  decide +kernel

def b0_s194 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead194 : impossible 6 0 b0_s194 := by
  apply by_search
  decide +kernel

def b0_s195 : List Sig := [raw3,raw4,raw0,b0_w48,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead195 : impossible 6 0 b0_s195 := by
  apply by_search
  decide +kernel

def b0_s196 : List Sig := [raw3,raw4,raw0,b0_w48,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead196 : impossible 6 0 b0_s196 := by
  apply by_search
  decide +kernel

def b0_s197 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w49]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead197 : impossible 6 0 b0_s197 := by
  apply by_search
  decide +kernel

def b0_s198 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,raw1,b0_w49]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead198 : impossible 6 0 b0_s198 := by
  apply by_search
  decide +kernel

def b0_s172 : List Sig := [raw3,raw4,raw0,raw2,b0_w5,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead172 : impossible 7 0 b0_s172 := by
  apply reject_branch 6 0 b0_s172 [] [[b0_w0,raw3,raw4,raw0,raw2,b0_w5,raw1],[b0_w1,raw3,raw4,raw0,raw2,b0_w5,raw1],[b0_w2,raw3,raw0,raw4,raw2,b0_w5,raw1],[b0_w3,raw3,raw0,raw4,raw2,b0_w5,raw1],[b0_w4,raw3,raw2,raw4,raw0,b0_w5,raw1],[b0_w6,raw3,raw1,raw4,raw0,raw2,b0_w5],[b0_w7,raw1,raw4,raw0,raw2,b0_w5],[b0_w7,raw3,raw1,raw4,raw0,raw2,b0_w5],[b0_w8,raw4,raw0,raw3,raw2,b0_w5,raw1],[b0_w9,raw4,raw0,raw3,raw2,b0_w5,raw1],[b0_w10,raw4,raw2,raw3,raw0,b0_w5,raw1],[b0_w11,raw4,raw2,raw3,raw0,b0_w5,raw1],[b0_w46,raw4,raw3,raw0,raw2,raw1],[b0_w46,raw4,b0_w5,raw3,raw0,raw2,raw1],[b0_w29,raw4,raw3,raw0,raw2,raw1],[b0_w29,raw4,b0_w5,raw3,raw0,raw2,raw1],[b0_w12,raw4,raw1,raw3,raw0,raw2,b0_w5],[b0_w13,raw4,raw1,raw3,raw0,raw2,b0_w5],[b0_w14,raw0,raw2,raw3,raw4,b0_w5,raw1],[b0_w15,raw0,raw3,raw4,b0_w5,raw1],[b0_w15,raw0,raw2,raw3,raw4,b0_w5,raw1],[b0_w47,raw0,raw3,raw4,raw2,raw1],[b0_w47,raw0,b0_w5,raw3,raw4,raw2,raw1],[b0_w39,raw0,raw3,raw4,raw2,raw1],[b0_w39,raw0,b0_w5,raw3,raw4,raw2,raw1],[b0_w16,raw0,raw1,raw3,raw4,raw2,b0_w5],[b0_w17,raw0,raw1,raw3,raw4,raw2,b0_w5],[b0_w18,raw2,raw1,raw3,raw4,raw0,b0_w5],[b0_w19,raw2,raw1,raw3,raw4,raw0,b0_w5],[b0_w48,raw1,raw3,raw4,raw0,raw2],[b0_w48,b0_w5,raw1,raw3,raw4,raw0,raw2],[b0_w49,raw1,raw3,raw4,raw0,raw2],[b0_w49,b0_w5,raw1,raw3,raw4,raw0,raw2]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead22
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead46
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead96
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead114
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead155
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead173
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead174
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead175
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead176
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead177
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead178
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead179
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead180
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead181
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead62
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead182
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead183
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead184
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead185
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead186
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead187
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead188
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead189
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead136
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead190
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead191
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead192
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead193
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead194
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead195
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead196
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead197
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead198
  · decide +kernel

def b0_s200 : List Sig := [b0_w24,b0_w6,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead200 : impossible 6 0 b0_s200 := by
  apply by_search
  decide +kernel

def b0_s201 : List Sig := [raw3,raw4,b0_w50,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead201 : impossible 6 0 b0_s201 := by
  apply by_search
  decide +kernel

def b0_s202 : List Sig := [b0_w6,raw3,raw4,b0_w50,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead202 : impossible 6 0 b0_s202 := by
  apply by_search
  decide +kernel

def b0_s203 : List Sig := [b0_w35,b0_w6,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead203 : impossible 6 0 b0_s203 := by
  apply by_search
  decide +kernel

def b0_s204 : List Sig := [raw3,raw4,raw0,b0_w51,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead204 : impossible 6 0 b0_s204 := by
  apply by_search
  decide +kernel

def b0_s205 : List Sig := [b0_w6,raw3,raw4,raw0,b0_w51,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead205 : impossible 6 0 b0_s205 := by
  apply by_search
  decide +kernel

def b0_s206 : List Sig := [b0_w44,b0_w6,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead206 : impossible 6 0 b0_s206 := by
  apply by_search
  decide +kernel

def b0_s207 : List Sig := [raw3,raw4,raw0,raw2,b0_w52,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead207 : impossible 6 0 b0_s207 := by
  apply by_search
  decide +kernel

def b0_s208 : List Sig := [b0_w6,raw3,raw4,raw0,raw2,b0_w52,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead208 : impossible 6 0 b0_s208 := by
  apply by_search
  decide +kernel

def b0_s209 : List Sig := [b0_w6,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead209 : impossible 6 0 b0_s209 := by
  apply by_search
  decide +kernel

def b0_s210 : List Sig := [b0_w6,raw3,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead210 : impossible 6 0 b0_s210 := by
  apply by_search
  decide +kernel

def b0_s211 : List Sig := [b0_w8,b0_w6,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead211 : impossible 6 0 b0_s211 := by
  apply by_search
  decide +kernel

def b0_s212 : List Sig := [b0_w6,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead212 : impossible 6 0 b0_s212 := by
  apply by_search
  decide +kernel

def b0_s213 : List Sig := [b0_w6,b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead213 : impossible 6 0 b0_s213 := by
  apply by_search
  decide +kernel

def b0_s214 : List Sig := [b0_w6,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead214 : impossible 6 0 b0_s214 := by
  apply by_search
  decide +kernel

def b0_s215 : List Sig := [b0_w6,b0_w12,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead215 : impossible 6 0 b0_s215 := by
  apply by_search
  decide +kernel

def b0_s216 : List Sig := [b0_w6,raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead216 : impossible 6 0 b0_s216 := by
  apply by_search
  decide +kernel

def b0_s217 : List Sig := [b0_w14,b0_w6,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead217 : impossible 6 0 b0_s217 := by
  apply by_search
  decide +kernel

def b0_s218 : List Sig := [b0_w6,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead218 : impossible 6 0 b0_s218 := by
  apply by_search
  decide +kernel

def b0_s219 : List Sig := [b0_w6,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead219 : impossible 6 0 b0_s219 := by
  apply by_search
  decide +kernel

def b0_s220 : List Sig := [b0_w6,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead220 : impossible 6 0 b0_s220 := by
  apply by_search
  decide +kernel

def b0_s221 : List Sig := [b0_w6,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead221 : impossible 6 0 b0_s221 := by
  apply by_search
  decide +kernel

def b0_s222 : List Sig := [b0_w6,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead222 : impossible 6 0 b0_s222 := by
  apply by_search
  decide +kernel

def b0_s223 : List Sig := [b0_w6,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead223 : impossible 6 0 b0_s223 := by
  apply by_search
  decide +kernel

def b0_s199 : List Sig := [b0_w6,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead199 : impossible 7 0 b0_s199 := by
  apply reject_branch 6 0 b0_s199 [] [[b0_w24,raw4,raw3,raw0,raw2,raw1],[b0_w24,b0_w6,raw4,raw3,raw0,raw2,raw1],[b0_w50,raw4,raw3,raw0,raw2,raw1],[b0_w50,b0_w6,raw4,raw3,raw0,raw2,raw1],[b0_w35,raw0,raw3,raw4,raw2,raw1],[b0_w35,b0_w6,raw0,raw3,raw4,raw2,raw1],[b0_w51,raw0,raw3,raw4,raw2,raw1],[b0_w51,b0_w6,raw0,raw3,raw4,raw2,raw1],[b0_w44,raw2,raw3,raw4,raw0,raw1],[b0_w44,b0_w6,raw2,raw3,raw4,raw0,raw1],[b0_w52,raw2,raw3,raw4,raw0,raw1],[b0_w52,b0_w6,raw2,raw3,raw4,raw0,raw1],[b0_w0,raw3,raw4,b0_w6,raw0,raw2,raw1],[b0_w1,raw3,raw4,b0_w6,raw0,raw2,raw1],[b0_w2,raw3,raw0,b0_w6,raw4,raw2,raw1],[b0_w3,raw3,raw0,b0_w6,raw4,raw2,raw1],[b0_w4,raw3,raw2,b0_w6,raw4,raw0,raw1],[b0_w5,raw3,raw2,b0_w6,raw4,raw0,raw1],[b0_w7,raw1,b0_w6,raw4,raw0,raw2],[b0_w7,raw3,raw1,b0_w6,raw4,raw0,raw2],[b0_w8,raw4,raw0,b0_w6,raw3,raw2,raw1],[b0_w9,raw4,raw0,b0_w6,raw3,raw2,raw1],[b0_w10,raw4,raw2,b0_w6,raw3,raw0,raw1],[b0_w11,raw4,raw2,b0_w6,raw3,raw0,raw1],[b0_w12,raw4,raw1,b0_w6,raw3,raw0,raw2],[b0_w13,raw4,raw1,b0_w6,raw3,raw0,raw2],[b0_w14,raw0,raw2,b0_w6,raw3,raw4,raw1],[b0_w15,raw0,b0_w6,raw3,raw4,raw1],[b0_w15,raw0,raw2,b0_w6,raw3,raw4,raw1],[b0_w16,raw0,raw1,b0_w6,raw3,raw4,raw2],[b0_w17,raw0,raw1,b0_w6,raw3,raw4,raw2],[b0_w18,raw2,raw1,b0_w6,raw3,raw4,raw0],[b0_w19,raw2,raw1,b0_w6,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead10
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead200
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead201
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead202
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead87
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead203
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead204
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead205
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead151
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead206
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead207
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead208
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead23
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead47
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead97
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead115
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead156
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead173
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead209
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead210
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead211
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead212
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead213
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead214
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead215
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead216
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead217
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead218
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead219
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead220
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead221
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead222
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead223
  · decide +kernel

def b0_s225 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead225 : impossible 6 0 b0_s225 := by
  apply by_search
  decide +kernel

def b0_s226 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead226 : impossible 6 0 b0_s226 := by
  apply by_search
  decide +kernel

def b0_s227 : List Sig := [b0_w10,raw3,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead227 : impossible 6 0 b0_s227 := by
  apply by_search
  decide +kernel

def b0_s228 : List Sig := [raw3,raw4,raw0,raw2,b0_w11,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead228 : impossible 6 0 b0_s228 := by
  apply by_search
  decide +kernel

def b0_s229 : List Sig := [b0_w12,raw3,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead229 : impossible 6 0 b0_s229 := by
  apply by_search
  decide +kernel

def b0_s230 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w7,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead230 : impossible 6 0 b0_s230 := by
  apply by_search
  decide +kernel

def b0_s231 : List Sig := [raw3,b0_w53,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead231 : impossible 6 0 b0_s231 := by
  apply by_search
  decide +kernel

def b0_s232 : List Sig := [raw3,b0_w53,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead232 : impossible 6 0 b0_s232 := by
  apply by_search
  decide +kernel

def b0_s233 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w7,b0_w31]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead233 : impossible 6 0 b0_s233 := by
  apply by_search
  decide +kernel

def b0_s234 : List Sig := [b0_w14,raw3,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead234 : impossible 6 0 b0_s234 := by
  apply by_search
  decide +kernel

def b0_s235 : List Sig := [raw3,raw4,raw0,raw1,b0_w15,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead235 : impossible 6 0 b0_s235 := by
  apply by_search
  decide +kernel

def b0_s236 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w15,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead236 : impossible 6 0 b0_s236 := by
  apply by_search
  decide +kernel

def b0_s237 : List Sig := [raw3,raw4,b0_w16,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead237 : impossible 6 0 b0_s237 := by
  apply by_search
  decide +kernel

def b0_s238 : List Sig := [raw3,raw4,raw0,raw2,b0_w17,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead238 : impossible 6 0 b0_s238 := by
  apply by_search
  decide +kernel

def b0_s239 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w17,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead239 : impossible 6 0 b0_s239 := by
  apply by_search
  decide +kernel

def b0_s240 : List Sig := [raw3,raw4,b0_w54,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead240 : impossible 6 0 b0_s240 := by
  apply by_search
  decide +kernel

def b0_s241 : List Sig := [raw3,raw4,b0_w54,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead241 : impossible 6 0 b0_s241 := by
  apply by_search
  decide +kernel

def b0_s242 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w7,b0_w41]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead242 : impossible 6 0 b0_s242 := by
  apply by_search
  decide +kernel

def b0_s243 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead243 : impossible 6 0 b0_s243 := by
  apply by_search
  decide +kernel

def b0_s244 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w19,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead244 : impossible 6 0 b0_s244 := by
  apply by_search
  decide +kernel

def b0_s245 : List Sig := [raw3,raw4,raw0,b0_w55,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead245 : impossible 6 0 b0_s245 := by
  apply by_search
  decide +kernel

def b0_s246 : List Sig := [raw3,raw4,raw0,b0_w55,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead246 : impossible 6 0 b0_s246 := by
  apply by_search
  decide +kernel

def b0_s247 : List Sig := [raw3,raw4,raw0,b0_w55,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead247 : impossible 6 0 b0_s247 := by
  apply by_search
  decide +kernel

def b0_s248 : List Sig := [raw3,raw4,raw0,b0_w55,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead248 : impossible 6 0 b0_s248 := by
  apply by_search
  decide +kernel

def b0_s249 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w7,b0_w49]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead249 : impossible 6 0 b0_s249 := by
  apply by_search
  decide +kernel

def b0_s224 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w7]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead224 : impossible 7 0 b0_s224 := by
  apply reject_branch 6 0 b0_s224 [] [[b0_w0,raw4,raw0,raw2,raw1,b0_w7],[b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w7],[b0_w1,raw3,raw4,raw0,raw2,raw1,b0_w7],[b0_w2,raw3,raw0,raw4,raw2,raw1,b0_w7],[b0_w3,raw0,raw4,raw2,raw1,b0_w7],[b0_w3,raw3,raw0,raw4,raw2,raw1,b0_w7],[b0_w4,raw3,raw2,raw4,raw0,raw1,b0_w7],[b0_w5,raw2,raw4,raw0,raw1,b0_w7],[b0_w5,raw3,raw2,raw4,raw0,raw1,b0_w7],[b0_w6,raw1,raw4,raw0,raw2,b0_w7],[b0_w6,raw3,raw1,raw4,raw0,raw2,b0_w7],[b0_w8,raw4,raw0,raw3,raw2,raw1,b0_w7],[b0_w9,raw4,raw0,raw3,raw2,raw1,b0_w7],[b0_w10,raw4,raw2,raw3,raw0,raw1,b0_w7],[b0_w11,raw4,raw2,raw3,raw0,raw1,b0_w7],[b0_w12,raw4,raw1,raw3,raw0,raw2,b0_w7],[b0_w13,raw4,raw1,raw3,raw0,raw2,b0_w7],[b0_w53,raw4,raw3,raw0,raw2,raw1],[b0_w53,raw4,b0_w7,raw3,raw0,raw2,raw1],[b0_w31,raw4,raw3,raw0,raw2,raw1],[b0_w31,raw4,b0_w7,raw3,raw0,raw2,raw1],[b0_w14,raw0,raw2,raw3,raw4,raw1,b0_w7],[b0_w15,raw0,raw3,raw4,raw1,b0_w7],[b0_w15,raw0,raw2,raw3,raw4,raw1,b0_w7],[b0_w16,raw0,raw1,raw3,raw4,raw2,b0_w7],[b0_w17,raw0,raw3,raw4,raw2,b0_w7],[b0_w17,raw0,raw1,raw3,raw4,raw2,b0_w7],[b0_w54,raw0,raw3,raw4,raw2,raw1],[b0_w54,raw0,b0_w7,raw3,raw4,raw2,raw1],[b0_w41,raw0,raw3,raw4,raw2,raw1],[b0_w41,raw0,b0_w7,raw3,raw4,raw2,raw1],[b0_w18,raw2,raw1,raw3,raw4,raw0,b0_w7],[b0_w19,raw2,raw1,raw3,raw4,raw0,b0_w7],[b0_w55,raw3,raw4,raw0,raw1],[b0_w55,raw2,raw3,raw4,raw0,raw1],[b0_w55,b0_w7,raw3,raw4,raw0,raw1],[b0_w55,raw2,b0_w7,raw3,raw4,raw0,raw1],[b0_w49,raw2,raw3,raw4,raw0,raw1],[b0_w49,raw2,b0_w7,raw3,raw4,raw0,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead24
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead25
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead48
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead98
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead116
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead117
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead157
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead174
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead175
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead209
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead210
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead225
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead226
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead227
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead228
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead229
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead230
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead231
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead232
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead66
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead233
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead234
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead235
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead236
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead237
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead238
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead239
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead240
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead241
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead140
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead242
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead243
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead244
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead245
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead246
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead247
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead248
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead197
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead249
  · decide +kernel

def b0_s251 : List Sig := [b0_w20,b0_w8,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead251 : impossible 6 0 b0_s251 := by
  apply by_search
  decide +kernel

def b0_s252 : List Sig := [b0_w56,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead252 : impossible 6 0 b0_s252 := by
  apply by_search
  decide +kernel

def b0_s253 : List Sig := [b0_w8,b0_w56,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead253 : impossible 6 0 b0_s253 := by
  apply by_search
  decide +kernel

def b0_s254 : List Sig := [raw3,b0_w56,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead254 : impossible 6 0 b0_s254 := by
  apply by_search
  decide +kernel

def b0_s255 : List Sig := [b0_w8,raw3,b0_w56,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead255 : impossible 6 0 b0_s255 := by
  apply by_search
  decide +kernel

def b0_s256 : List Sig := [b0_w57,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead256 : impossible 6 0 b0_s256 := by
  apply by_search
  decide +kernel

def b0_s257 : List Sig := [b0_w57,b0_w8,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead257 : impossible 6 0 b0_s257 := by
  apply by_search
  decide +kernel

def b0_s258 : List Sig := [raw3,raw4,raw0,b0_w58,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead258 : impossible 6 0 b0_s258 := by
  apply by_search
  decide +kernel

def b0_s259 : List Sig := [b0_w8,raw3,raw4,raw0,b0_w58,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead259 : impossible 6 0 b0_s259 := by
  apply by_search
  decide +kernel

def b0_s260 : List Sig := [raw3,raw4,raw0,raw2,b0_w58,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead260 : impossible 6 0 b0_s260 := by
  apply by_search
  decide +kernel

def b0_s261 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,b0_w58,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead261 : impossible 6 0 b0_s261 := by
  apply by_search
  decide +kernel

def b0_s262 : List Sig := [b0_w59,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead262 : impossible 6 0 b0_s262 := by
  apply by_search
  decide +kernel

def b0_s263 : List Sig := [b0_w59,b0_w8,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead263 : impossible 6 0 b0_s263 := by
  apply by_search
  decide +kernel

def b0_s264 : List Sig := [raw3,raw4,raw0,raw2,b0_w60]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead264 : impossible 6 0 b0_s264 := by
  apply by_search
  decide +kernel

def b0_s265 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,b0_w60]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead265 : impossible 6 0 b0_s265 := by
  apply by_search
  decide +kernel

def b0_s266 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w60]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead266 : impossible 6 0 b0_s266 := by
  apply by_search
  decide +kernel

def b0_s267 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,raw1,b0_w60]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead267 : impossible 6 0 b0_s267 := by
  apply by_search
  decide +kernel

def b0_s268 : List Sig := [b0_w8,raw3,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead268 : impossible 6 0 b0_s268 := by
  apply by_search
  decide +kernel

def b0_s269 : List Sig := [b0_w8,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead269 : impossible 6 0 b0_s269 := by
  apply by_search
  decide +kernel

def b0_s270 : List Sig := [b0_w8,b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead270 : impossible 6 0 b0_s270 := by
  apply by_search
  decide +kernel

def b0_s271 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead271 : impossible 6 0 b0_s271 := by
  apply by_search
  decide +kernel

def b0_s272 : List Sig := [b0_w8,b0_w12,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead272 : impossible 6 0 b0_s272 := by
  apply by_search
  decide +kernel

def b0_s273 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead273 : impossible 6 0 b0_s273 := by
  apply by_search
  decide +kernel

def b0_s274 : List Sig := [b0_w14,b0_w8,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead274 : impossible 6 0 b0_s274 := by
  apply by_search
  decide +kernel

def b0_s275 : List Sig := [b0_w8,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead275 : impossible 6 0 b0_s275 := by
  apply by_search
  decide +kernel

def b0_s276 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead276 : impossible 6 0 b0_s276 := by
  apply by_search
  decide +kernel

def b0_s277 : List Sig := [b0_w8,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead277 : impossible 6 0 b0_s277 := by
  apply by_search
  decide +kernel

def b0_s278 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead278 : impossible 6 0 b0_s278 := by
  apply by_search
  decide +kernel

def b0_s279 : List Sig := [b0_w8,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead279 : impossible 6 0 b0_s279 := by
  apply by_search
  decide +kernel

def b0_s280 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead280 : impossible 6 0 b0_s280 := by
  apply by_search
  decide +kernel

def b0_s250 : List Sig := [b0_w8,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead250 : impossible 7 0 b0_s250 := by
  apply reject_branch 6 0 b0_s250 [] [[b0_w20,raw3,raw4,raw0,raw2,raw1],[b0_w20,b0_w8,raw3,raw4,raw0,raw2,raw1],[b0_w56,raw4,raw0,raw2,raw1],[b0_w56,b0_w8,raw4,raw0,raw2,raw1],[b0_w56,raw3,raw4,raw0,raw2,raw1],[b0_w56,b0_w8,raw3,raw4,raw0,raw2,raw1],[b0_w57,raw2,raw3,raw4,raw0,raw1],[b0_w57,b0_w8,raw2,raw3,raw4,raw0,raw1],[b0_w58,raw3,raw4,raw0,raw1],[b0_w58,b0_w8,raw3,raw4,raw0,raw1],[b0_w58,raw2,raw3,raw4,raw0,raw1],[b0_w58,b0_w8,raw2,raw3,raw4,raw0,raw1],[b0_w59,raw1,raw3,raw4,raw0,raw2],[b0_w59,b0_w8,raw1,raw3,raw4,raw0,raw2],[b0_w60,raw3,raw4,raw0,raw2],[b0_w60,b0_w8,raw3,raw4,raw0,raw2],[b0_w60,raw1,raw3,raw4,raw0,raw2],[b0_w60,b0_w8,raw1,raw3,raw4,raw0,raw2],[b0_w0,raw3,b0_w8,raw0,raw2,raw1],[b0_w0,raw3,raw4,b0_w8,raw0,raw2,raw1],[b0_w1,raw3,raw4,b0_w8,raw0,raw2,raw1],[b0_w2,raw3,raw0,b0_w8,raw4,raw2,raw1],[b0_w3,raw3,raw0,b0_w8,raw4,raw2,raw1],[b0_w4,raw3,raw2,b0_w8,raw4,raw0,raw1],[b0_w5,raw3,raw2,b0_w8,raw4,raw0,raw1],[b0_w6,raw3,raw1,b0_w8,raw4,raw0,raw2],[b0_w7,raw3,raw1,b0_w8,raw4,raw0,raw2],[b0_w9,raw0,b0_w8,raw3,raw2,raw1],[b0_w9,raw4,raw0,b0_w8,raw3,raw2,raw1],[b0_w10,raw4,raw2,b0_w8,raw3,raw0,raw1],[b0_w11,raw4,raw2,b0_w8,raw3,raw0,raw1],[b0_w12,raw4,raw1,b0_w8,raw3,raw0,raw2],[b0_w13,raw4,raw1,b0_w8,raw3,raw0,raw2],[b0_w14,raw0,raw2,b0_w8,raw3,raw4,raw1],[b0_w15,raw0,b0_w8,raw3,raw4,raw1],[b0_w15,raw0,raw2,b0_w8,raw3,raw4,raw1],[b0_w16,raw0,raw1,b0_w8,raw3,raw4,raw2],[b0_w17,raw0,raw1,b0_w8,raw3,raw4,raw2],[b0_w18,raw2,raw1,b0_w8,raw3,raw4,raw0],[b0_w19,raw2,raw1,b0_w8,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead2
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead251
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead252
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead253
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead254
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead255
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead256
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead257
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead258
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead259
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead260
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead261
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead262
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead263
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead264
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead265
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead266
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead267
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead26
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead27
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead49
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead99
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead118
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead158
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead176
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead211
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead225
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead268
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead269
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead270
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead271
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead272
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead273
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead274
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead275
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead276
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead277
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead278
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead279
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead280
  · decide +kernel

def b0_s282 : List Sig := [b0_w61,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead282 : impossible 6 0 b0_s282 := by
  apply by_search
  decide +kernel

def b0_s283 : List Sig := [b0_w61,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead283 : impossible 6 0 b0_s283 := by
  apply by_search
  decide +kernel

def b0_s284 : List Sig := [b0_w61,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead284 : impossible 6 0 b0_s284 := by
  apply by_search
  decide +kernel

def b0_s285 : List Sig := [b0_w61,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead285 : impossible 6 0 b0_s285 := by
  apply by_search
  decide +kernel

def b0_s286 : List Sig := [raw3,raw4,raw0,b0_w9,b0_w27,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead286 : impossible 6 0 b0_s286 := by
  apply by_search
  decide +kernel

def b0_s287 : List Sig := [b0_w10,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead287 : impossible 6 0 b0_s287 := by
  apply by_search
  decide +kernel

def b0_s288 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead288 : impossible 6 0 b0_s288 := by
  apply by_search
  decide +kernel

def b0_s289 : List Sig := [b0_w12,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead289 : impossible 6 0 b0_s289 := by
  apply by_search
  decide +kernel

def b0_s290 : List Sig := [raw3,raw0,b0_w9,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead290 : impossible 6 0 b0_s290 := by
  apply by_search
  decide +kernel

def b0_s291 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead291 : impossible 6 0 b0_s291 := by
  apply by_search
  decide +kernel

def b0_s292 : List Sig := [b0_w14,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead292 : impossible 6 0 b0_s292 := by
  apply by_search
  decide +kernel

def b0_s293 : List Sig := [raw3,raw4,raw0,b0_w9,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead293 : impossible 6 0 b0_s293 := by
  apply by_search
  decide +kernel

def b0_s294 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead294 : impossible 6 0 b0_s294 := by
  apply by_search
  decide +kernel

def b0_s295 : List Sig := [raw3,raw4,b0_w16,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead295 : impossible 6 0 b0_s295 := by
  apply by_search
  decide +kernel

def b0_s296 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead296 : impossible 6 0 b0_s296 := by
  apply by_search
  decide +kernel

def b0_s297 : List Sig := [b0_w62,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead297 : impossible 6 0 b0_s297 := by
  apply by_search
  decide +kernel

def b0_s298 : List Sig := [b0_w62,raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead298 : impossible 6 0 b0_s298 := by
  apply by_search
  decide +kernel

def b0_s299 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w63]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead299 : impossible 6 0 b0_s299 := by
  apply by_search
  decide +kernel

def b0_s300 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,raw1,b0_w63]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead300 : impossible 6 0 b0_s300 := by
  apply by_search
  decide +kernel

def b0_s301 : List Sig := [raw3,raw4,raw0,b0_w64,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead301 : impossible 6 0 b0_s301 := by
  apply by_search
  decide +kernel

def b0_s302 : List Sig := [raw3,raw4,raw0,b0_w64,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead302 : impossible 6 0 b0_s302 := by
  apply by_search
  decide +kernel

def b0_s303 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w65]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead303 : impossible 6 0 b0_s303 := by
  apply by_search
  decide +kernel

def b0_s304 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,raw1,b0_w65]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead304 : impossible 6 0 b0_s304 := by
  apply by_search
  decide +kernel

def b0_s305 : List Sig := [raw3,raw4,raw0,b0_w9,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead305 : impossible 6 0 b0_s305 := by
  apply by_search
  decide +kernel

def b0_s306 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead306 : impossible 6 0 b0_s306 := by
  apply by_search
  decide +kernel

def b0_s281 : List Sig := [raw3,raw4,raw0,b0_w9,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead281 : impossible 7 0 b0_s281 := by
  apply reject_branch 6 0 b0_s281 [] [[b0_w0,raw3,raw4,raw0,b0_w9,raw2,raw1],[b0_w1,raw3,raw0,b0_w9,raw2,raw1],[b0_w1,raw3,raw4,raw0,b0_w9,raw2,raw1],[b0_w2,raw3,raw0,raw4,b0_w9,raw2,raw1],[b0_w3,raw3,raw0,raw4,b0_w9,raw2,raw1],[b0_w61,raw4,raw0,raw2,raw1],[b0_w61,raw3,raw4,raw0,raw2,raw1],[b0_w61,b0_w9,raw4,raw0,raw2,raw1],[b0_w61,raw3,b0_w9,raw4,raw0,raw2,raw1],[b0_w27,raw3,raw4,raw0,raw2,raw1],[b0_w27,raw3,b0_w9,raw4,raw0,raw2,raw1],[b0_w4,raw3,raw2,raw4,raw0,b0_w9,raw1],[b0_w5,raw3,raw2,raw4,raw0,b0_w9,raw1],[b0_w6,raw3,raw1,raw4,raw0,b0_w9,raw2],[b0_w7,raw3,raw1,raw4,raw0,b0_w9,raw2],[b0_w8,raw0,raw3,b0_w9,raw2,raw1],[b0_w8,raw4,raw0,raw3,b0_w9,raw2,raw1],[b0_w10,raw4,raw2,raw3,raw0,b0_w9,raw1],[b0_w11,raw4,raw2,raw3,raw0,b0_w9,raw1],[b0_w12,raw4,raw1,raw3,raw0,b0_w9,raw2],[b0_w13,raw1,raw3,raw0,b0_w9,raw2],[b0_w13,raw4,raw1,raw3,raw0,b0_w9,raw2],[b0_w14,raw0,raw2,raw3,raw4,b0_w9,raw1],[b0_w15,raw0,raw3,raw4,b0_w9,raw1],[b0_w15,raw0,raw2,raw3,raw4,b0_w9,raw1],[b0_w16,raw0,raw1,raw3,raw4,b0_w9,raw2],[b0_w17,raw0,raw1,raw3,raw4,b0_w9,raw2],[b0_w62,raw2,raw3,raw4,raw0,raw1],[b0_w62,b0_w9,raw2,raw3,raw4,raw0,raw1],[b0_w63,raw2,raw3,raw4,raw0,raw1],[b0_w63,b0_w9,raw2,raw3,raw4,raw0,raw1],[b0_w64,raw1,raw3,raw4,raw0,raw2],[b0_w64,b0_w9,raw1,raw3,raw4,raw0,raw2],[b0_w65,raw1,raw3,raw4,raw0,raw2],[b0_w65,b0_w9,raw1,raw3,raw4,raw0,raw2],[b0_w18,raw2,raw1,raw3,raw4,raw0,b0_w9],[b0_w19,raw2,raw1,raw3,raw4,raw0,b0_w9]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead28
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead50
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead51
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead100
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead119
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead282
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead283
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead284
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead285
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead58
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead286
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead159
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead177
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead212
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead226
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead268
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead269
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead287
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead288
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead289
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead290
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead291
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead292
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead293
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead294
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead295
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead296
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead297
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead298
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead299
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead300
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead301
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead302
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead303
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead304
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead305
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead306
  · decide +kernel

def b0_s308 : List Sig := [b0_w22,b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead308 : impossible 6 0 b0_s308 := by
  apply by_search
  decide +kernel

def b0_s309 : List Sig := [raw3,b0_w66,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead309 : impossible 6 0 b0_s309 := by
  apply by_search
  decide +kernel

def b0_s310 : List Sig := [b0_w10,raw3,b0_w66,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead310 : impossible 6 0 b0_s310 := by
  apply by_search
  decide +kernel

def b0_s311 : List Sig := [b0_w57,b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead311 : impossible 6 0 b0_s311 := by
  apply by_search
  decide +kernel

def b0_s312 : List Sig := [raw3,raw4,raw0,b0_w67,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead312 : impossible 6 0 b0_s312 := by
  apply by_search
  decide +kernel

def b0_s313 : List Sig := [b0_w10,raw3,raw4,raw0,b0_w67,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead313 : impossible 6 0 b0_s313 := by
  apply by_search
  decide +kernel

def b0_s314 : List Sig := [b0_w68,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead314 : impossible 6 0 b0_s314 := by
  apply by_search
  decide +kernel

def b0_s315 : List Sig := [b0_w68,b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead315 : impossible 6 0 b0_s315 := by
  apply by_search
  decide +kernel

def b0_s316 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w69]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead316 : impossible 6 0 b0_s316 := by
  apply by_search
  decide +kernel

def b0_s317 : List Sig := [b0_w10,raw3,raw4,raw0,raw2,raw1,b0_w69]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead317 : impossible 6 0 b0_s317 := by
  apply by_search
  decide +kernel

def b0_s318 : List Sig := [b0_w10,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead318 : impossible 6 0 b0_s318 := by
  apply by_search
  decide +kernel

def b0_s319 : List Sig := [b0_w12,b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead319 : impossible 6 0 b0_s319 := by
  apply by_search
  decide +kernel

def b0_s320 : List Sig := [b0_w10,raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead320 : impossible 6 0 b0_s320 := by
  apply by_search
  decide +kernel

def b0_s321 : List Sig := [b0_w14,b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead321 : impossible 6 0 b0_s321 := by
  apply by_search
  decide +kernel

def b0_s322 : List Sig := [b0_w10,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead322 : impossible 6 0 b0_s322 := by
  apply by_search
  decide +kernel

def b0_s323 : List Sig := [b0_w10,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead323 : impossible 6 0 b0_s323 := by
  apply by_search
  decide +kernel

def b0_s324 : List Sig := [b0_w10,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead324 : impossible 6 0 b0_s324 := by
  apply by_search
  decide +kernel

def b0_s325 : List Sig := [b0_w10,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead325 : impossible 6 0 b0_s325 := by
  apply by_search
  decide +kernel

def b0_s326 : List Sig := [b0_w10,raw3,raw4,raw0,b0_w18,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead326 : impossible 6 0 b0_s326 := by
  apply by_search
  decide +kernel

def b0_s327 : List Sig := [b0_w10,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead327 : impossible 6 0 b0_s327 := by
  apply by_search
  decide +kernel

def b0_s328 : List Sig := [b0_w10,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead328 : impossible 6 0 b0_s328 := by
  apply by_search
  decide +kernel

def b0_s307 : List Sig := [b0_w10,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead307 : impossible 7 0 b0_s307 := by
  apply reject_branch 6 0 b0_s307 [] [[b0_w22,raw3,raw4,raw0,raw2,raw1],[b0_w22,b0_w10,raw3,raw4,raw0,raw2,raw1],[b0_w66,raw3,raw4,raw0,raw2,raw1],[b0_w66,b0_w10,raw3,raw4,raw0,raw2,raw1],[b0_w57,raw0,raw3,raw4,raw2,raw1],[b0_w57,b0_w10,raw0,raw3,raw4,raw2,raw1],[b0_w67,raw0,raw3,raw4,raw2,raw1],[b0_w67,b0_w10,raw0,raw3,raw4,raw2,raw1],[b0_w68,raw1,raw3,raw4,raw0,raw2],[b0_w68,b0_w10,raw1,raw3,raw4,raw0,raw2],[b0_w69,raw1,raw3,raw4,raw0,raw2],[b0_w69,b0_w10,raw1,raw3,raw4,raw0,raw2],[b0_w0,raw3,raw4,b0_w10,raw0,raw2,raw1],[b0_w1,raw3,raw4,b0_w10,raw0,raw2,raw1],[b0_w2,raw3,raw0,b0_w10,raw4,raw2,raw1],[b0_w3,raw3,raw0,b0_w10,raw4,raw2,raw1],[b0_w4,raw3,raw2,b0_w10,raw4,raw0,raw1],[b0_w5,raw3,raw2,b0_w10,raw4,raw0,raw1],[b0_w6,raw3,raw1,b0_w10,raw4,raw0,raw2],[b0_w7,raw3,raw1,b0_w10,raw4,raw0,raw2],[b0_w8,raw4,raw0,b0_w10,raw3,raw2,raw1],[b0_w9,raw4,raw0,b0_w10,raw3,raw2,raw1],[b0_w11,raw4,raw2,b0_w10,raw3,raw0,raw1],[b0_w12,raw4,raw1,b0_w10,raw3,raw0,raw2],[b0_w13,raw4,raw1,b0_w10,raw3,raw0,raw2],[b0_w14,raw0,raw2,b0_w10,raw3,raw4,raw1],[b0_w15,raw0,b0_w10,raw3,raw4,raw1],[b0_w15,raw0,raw2,b0_w10,raw3,raw4,raw1],[b0_w16,raw0,raw1,b0_w10,raw3,raw4,raw2],[b0_w17,raw0,raw1,b0_w10,raw3,raw4,raw2],[b0_w18,raw1,b0_w10,raw3,raw4,raw0],[b0_w18,raw2,raw1,b0_w10,raw3,raw4,raw0],[b0_w19,raw2,raw1,b0_w10,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead6
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead308
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead309
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead310
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead256
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead311
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead312
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead313
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead314
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead315
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead316
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead317
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead29
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead52
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead101
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead125
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead160
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead178
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead213
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead227
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead270
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead287
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead318
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead319
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead320
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead321
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead322
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead323
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead324
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead325
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead326
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead327
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead328
  · decide +kernel

def b0_s330 : List Sig := [b0_w70,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead330 : impossible 6 0 b0_s330 := by
  apply by_search
  decide +kernel

def b0_s331 : List Sig := [b0_w70,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead331 : impossible 6 0 b0_s331 := by
  apply by_search
  decide +kernel

def b0_s332 : List Sig := [raw3,raw4,raw0,raw2,b0_w11,b0_w29,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead332 : impossible 6 0 b0_s332 := by
  apply by_search
  decide +kernel

def b0_s333 : List Sig := [b0_w12,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead333 : impossible 6 0 b0_s333 := by
  apply by_search
  decide +kernel

def b0_s334 : List Sig := [raw3,raw0,raw2,b0_w11,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead334 : impossible 6 0 b0_s334 := by
  apply by_search
  decide +kernel

def b0_s335 : List Sig := [raw3,raw4,raw0,raw2,b0_w11,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead335 : impossible 6 0 b0_s335 := by
  apply by_search
  decide +kernel

def b0_s336 : List Sig := [b0_w14,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead336 : impossible 6 0 b0_s336 := by
  apply by_search
  decide +kernel

def b0_s337 : List Sig := [raw3,raw4,raw0,b0_w11,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead337 : impossible 6 0 b0_s337 := by
  apply by_search
  decide +kernel

def b0_s338 : List Sig := [raw3,raw4,raw0,raw2,b0_w11,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead338 : impossible 6 0 b0_s338 := by
  apply by_search
  decide +kernel

def b0_s339 : List Sig := [b0_w71,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead339 : impossible 6 0 b0_s339 := by
  apply by_search
  decide +kernel

def b0_s340 : List Sig := [b0_w71,raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead340 : impossible 6 0 b0_s340 := by
  apply by_search
  decide +kernel

def b0_s341 : List Sig := [raw3,raw4,raw0,raw2,b0_w11,raw1,b0_w63]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead341 : impossible 6 0 b0_s341 := by
  apply by_search
  decide +kernel

def b0_s342 : List Sig := [raw3,raw4,b0_w16,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead342 : impossible 6 0 b0_s342 := by
  apply by_search
  decide +kernel

def b0_s343 : List Sig := [raw3,raw4,raw0,raw2,b0_w11,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead343 : impossible 6 0 b0_s343 := by
  apply by_search
  decide +kernel

def b0_s344 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead344 : impossible 6 0 b0_s344 := by
  apply by_search
  decide +kernel

def b0_s345 : List Sig := [raw3,raw4,raw0,raw2,b0_w11,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead345 : impossible 6 0 b0_s345 := by
  apply by_search
  decide +kernel

def b0_s346 : List Sig := [raw3,raw4,raw0,b0_w72,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead346 : impossible 6 0 b0_s346 := by
  apply by_search
  decide +kernel

def b0_s347 : List Sig := [raw3,raw4,raw0,b0_w72,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead347 : impossible 6 0 b0_s347 := by
  apply by_search
  decide +kernel

def b0_s348 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w73]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead348 : impossible 6 0 b0_s348 := by
  apply by_search
  decide +kernel

def b0_s349 : List Sig := [raw3,raw4,raw0,raw2,b0_w11,raw1,b0_w73]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead349 : impossible 6 0 b0_s349 := by
  apply by_search
  decide +kernel

def b0_s329 : List Sig := [raw3,raw4,raw0,raw2,b0_w11,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead329 : impossible 7 0 b0_s329 := by
  apply reject_branch 6 0 b0_s329 [] [[b0_w0,raw3,raw4,raw0,raw2,b0_w11,raw1],[b0_w1,raw3,raw4,raw0,raw2,b0_w11,raw1],[b0_w2,raw3,raw0,raw4,raw2,b0_w11,raw1],[b0_w3,raw3,raw0,raw4,raw2,b0_w11,raw1],[b0_w4,raw3,raw2,raw4,raw0,b0_w11,raw1],[b0_w5,raw3,raw2,raw4,raw0,b0_w11,raw1],[b0_w70,raw3,raw4,raw0,raw2,raw1],[b0_w70,raw3,b0_w11,raw4,raw0,raw2,raw1],[b0_w29,raw3,raw4,raw0,raw2,raw1],[b0_w29,raw3,b0_w11,raw4,raw0,raw2,raw1],[b0_w6,raw3,raw1,raw4,raw0,raw2,b0_w11],[b0_w7,raw3,raw1,raw4,raw0,raw2,b0_w11],[b0_w8,raw4,raw0,raw3,raw2,b0_w11,raw1],[b0_w9,raw4,raw0,raw3,raw2,b0_w11,raw1],[b0_w10,raw4,raw2,raw3,raw0,b0_w11,raw1],[b0_w12,raw4,raw1,raw3,raw0,raw2,b0_w11],[b0_w13,raw1,raw3,raw0,raw2,b0_w11],[b0_w13,raw4,raw1,raw3,raw0,raw2,b0_w11],[b0_w14,raw0,raw2,raw3,raw4,b0_w11,raw1],[b0_w15,raw0,raw3,raw4,b0_w11,raw1],[b0_w15,raw0,raw2,raw3,raw4,b0_w11,raw1],[b0_w71,raw0,raw3,raw4,raw2,raw1],[b0_w71,raw0,b0_w11,raw3,raw4,raw2,raw1],[b0_w63,raw0,raw3,raw4,raw2,raw1],[b0_w63,raw0,b0_w11,raw3,raw4,raw2,raw1],[b0_w16,raw0,raw1,raw3,raw4,raw2,b0_w11],[b0_w17,raw0,raw1,raw3,raw4,raw2,b0_w11],[b0_w18,raw2,raw1,raw3,raw4,raw0,b0_w11],[b0_w19,raw2,raw1,raw3,raw4,raw0,b0_w11],[b0_w72,raw1,raw3,raw4,raw0,raw2],[b0_w72,b0_w11,raw1,raw3,raw4,raw0,raw2],[b0_w73,raw1,raw3,raw4,raw0,raw2],[b0_w73,b0_w11,raw1,raw3,raw4,raw0,raw2]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead30
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead53
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead102
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead126
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead161
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead179
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead330
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead331
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead62
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead332
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead214
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead228
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead271
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead288
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead318
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead333
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead334
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead335
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead336
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead337
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead338
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead339
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead340
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead299
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead341
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead342
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead343
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead344
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead345
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead346
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead347
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead348
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead349
  · decide +kernel

def b0_s351 : List Sig := [b0_w24,b0_w12,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead351 : impossible 6 0 b0_s351 := by
  apply by_search
  decide +kernel

def b0_s352 : List Sig := [raw3,b0_w74,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead352 : impossible 6 0 b0_s352 := by
  apply by_search
  decide +kernel

def b0_s353 : List Sig := [b0_w12,raw3,b0_w74,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead353 : impossible 6 0 b0_s353 := by
  apply by_search
  decide +kernel

def b0_s354 : List Sig := [b0_w59,b0_w12,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead354 : impossible 6 0 b0_s354 := by
  apply by_search
  decide +kernel

def b0_s355 : List Sig := [raw3,raw4,raw0,b0_w75,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead355 : impossible 6 0 b0_s355 := by
  apply by_search
  decide +kernel

def b0_s356 : List Sig := [b0_w12,raw3,raw4,raw0,b0_w75,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead356 : impossible 6 0 b0_s356 := by
  apply by_search
  decide +kernel

def b0_s357 : List Sig := [b0_w68,b0_w12,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead357 : impossible 6 0 b0_s357 := by
  apply by_search
  decide +kernel

def b0_s358 : List Sig := [raw3,raw4,raw0,raw2,b0_w76,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead358 : impossible 6 0 b0_s358 := by
  apply by_search
  decide +kernel

def b0_s359 : List Sig := [b0_w12,raw3,raw4,raw0,raw2,b0_w76,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead359 : impossible 6 0 b0_s359 := by
  apply by_search
  decide +kernel

def b0_s360 : List Sig := [b0_w12,raw3,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead360 : impossible 6 0 b0_s360 := by
  apply by_search
  decide +kernel

def b0_s361 : List Sig := [b0_w12,raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead361 : impossible 6 0 b0_s361 := by
  apply by_search
  decide +kernel

def b0_s362 : List Sig := [b0_w14,b0_w12,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead362 : impossible 6 0 b0_s362 := by
  apply by_search
  decide +kernel

def b0_s363 : List Sig := [b0_w12,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead363 : impossible 6 0 b0_s363 := by
  apply by_search
  decide +kernel

def b0_s364 : List Sig := [b0_w12,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead364 : impossible 6 0 b0_s364 := by
  apply by_search
  decide +kernel

def b0_s365 : List Sig := [b0_w12,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead365 : impossible 6 0 b0_s365 := by
  apply by_search
  decide +kernel

def b0_s366 : List Sig := [b0_w12,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead366 : impossible 6 0 b0_s366 := by
  apply by_search
  decide +kernel

def b0_s367 : List Sig := [b0_w12,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead367 : impossible 6 0 b0_s367 := by
  apply by_search
  decide +kernel

def b0_s368 : List Sig := [b0_w12,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead368 : impossible 6 0 b0_s368 := by
  apply by_search
  decide +kernel

def b0_s350 : List Sig := [b0_w12,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead350 : impossible 7 0 b0_s350 := by
  apply reject_branch 6 0 b0_s350 [] [[b0_w24,raw3,raw4,raw0,raw2,raw1],[b0_w24,b0_w12,raw3,raw4,raw0,raw2,raw1],[b0_w74,raw3,raw4,raw0,raw2,raw1],[b0_w74,b0_w12,raw3,raw4,raw0,raw2,raw1],[b0_w59,raw0,raw3,raw4,raw2,raw1],[b0_w59,b0_w12,raw0,raw3,raw4,raw2,raw1],[b0_w75,raw0,raw3,raw4,raw2,raw1],[b0_w75,b0_w12,raw0,raw3,raw4,raw2,raw1],[b0_w68,raw2,raw3,raw4,raw0,raw1],[b0_w68,b0_w12,raw2,raw3,raw4,raw0,raw1],[b0_w76,raw2,raw3,raw4,raw0,raw1],[b0_w76,b0_w12,raw2,raw3,raw4,raw0,raw1],[b0_w0,raw3,raw4,b0_w12,raw0,raw2,raw1],[b0_w1,raw3,raw4,b0_w12,raw0,raw2,raw1],[b0_w2,raw3,raw0,b0_w12,raw4,raw2,raw1],[b0_w3,raw3,raw0,b0_w12,raw4,raw2,raw1],[b0_w4,raw3,raw2,b0_w12,raw4,raw0,raw1],[b0_w5,raw3,raw2,b0_w12,raw4,raw0,raw1],[b0_w6,raw3,raw1,b0_w12,raw4,raw0,raw2],[b0_w7,raw3,raw1,b0_w12,raw4,raw0,raw2],[b0_w8,raw4,raw0,b0_w12,raw3,raw2,raw1],[b0_w9,raw4,raw0,b0_w12,raw3,raw2,raw1],[b0_w10,raw4,raw2,b0_w12,raw3,raw0,raw1],[b0_w11,raw4,raw2,b0_w12,raw3,raw0,raw1],[b0_w13,raw1,b0_w12,raw3,raw0,raw2],[b0_w13,raw4,raw1,b0_w12,raw3,raw0,raw2],[b0_w14,raw0,raw2,b0_w12,raw3,raw4,raw1],[b0_w15,raw0,b0_w12,raw3,raw4,raw1],[b0_w15,raw0,raw2,b0_w12,raw3,raw4,raw1],[b0_w16,raw0,raw1,b0_w12,raw3,raw4,raw2],[b0_w17,raw0,raw1,b0_w12,raw3,raw4,raw2],[b0_w18,raw2,raw1,b0_w12,raw3,raw4,raw0],[b0_w19,raw2,raw1,b0_w12,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead10
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead351
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead352
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead353
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead262
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead354
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead355
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead356
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead314
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead357
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead358
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead359
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead31
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead54
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead103
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead127
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead162
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead183
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead215
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead229
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead272
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead289
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead319
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead333
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead360
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead361
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead362
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead363
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead364
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead365
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead366
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead367
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead368
  · decide +kernel

def b0_s370 : List Sig := [b0_w77,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead370 : impossible 6 0 b0_s370 := by
  apply by_search
  decide +kernel

def b0_s371 : List Sig := [b0_w77,raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead371 : impossible 6 0 b0_s371 := by
  apply by_search
  decide +kernel

def b0_s372 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w13,b0_w31]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead372 : impossible 6 0 b0_s372 := by
  apply by_search
  decide +kernel

def b0_s373 : List Sig := [b0_w14,raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead373 : impossible 6 0 b0_s373 := by
  apply by_search
  decide +kernel

def b0_s374 : List Sig := [raw3,raw4,raw0,raw1,b0_w15,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead374 : impossible 6 0 b0_s374 := by
  apply by_search
  decide +kernel

def b0_s375 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w15,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead375 : impossible 6 0 b0_s375 := by
  apply by_search
  decide +kernel

def b0_s376 : List Sig := [raw3,raw4,b0_w16,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead376 : impossible 6 0 b0_s376 := by
  apply by_search
  decide +kernel

def b0_s377 : List Sig := [raw3,raw4,raw0,raw2,b0_w17,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead377 : impossible 6 0 b0_s377 := by
  apply by_search
  decide +kernel

def b0_s378 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w17,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead378 : impossible 6 0 b0_s378 := by
  apply by_search
  decide +kernel

def b0_s379 : List Sig := [raw3,raw4,b0_w78,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead379 : impossible 6 0 b0_s379 := by
  apply by_search
  decide +kernel

def b0_s380 : List Sig := [raw3,raw4,b0_w78,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead380 : impossible 6 0 b0_s380 := by
  apply by_search
  decide +kernel

def b0_s381 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w13,b0_w65]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead381 : impossible 6 0 b0_s381 := by
  apply by_search
  decide +kernel

def b0_s382 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead382 : impossible 6 0 b0_s382 := by
  apply by_search
  decide +kernel

def b0_s383 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w19,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead383 : impossible 6 0 b0_s383 := by
  apply by_search
  decide +kernel

def b0_s384 : List Sig := [raw3,raw4,raw0,b0_w79,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead384 : impossible 6 0 b0_s384 := by
  apply by_search
  decide +kernel

def b0_s385 : List Sig := [raw3,raw4,raw0,b0_w79,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead385 : impossible 6 0 b0_s385 := by
  apply by_search
  decide +kernel

def b0_s386 : List Sig := [raw3,raw4,raw0,b0_w79,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead386 : impossible 6 0 b0_s386 := by
  apply by_search
  decide +kernel

def b0_s387 : List Sig := [raw3,raw4,raw0,b0_w79,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead387 : impossible 6 0 b0_s387 := by
  apply by_search
  decide +kernel

def b0_s388 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w13,b0_w73]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead388 : impossible 6 0 b0_s388 := by
  apply by_search
  decide +kernel

def b0_s369 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead369 : impossible 7 0 b0_s369 := by
  apply reject_branch 6 0 b0_s369 [] [[b0_w0,raw3,raw0,raw2,raw1,b0_w13],[b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w13],[b0_w1,raw3,raw4,raw0,raw2,raw1,b0_w13],[b0_w2,raw3,raw0,raw4,raw2,raw1,b0_w13],[b0_w3,raw3,raw0,raw4,raw2,raw1,b0_w13],[b0_w4,raw3,raw2,raw4,raw0,raw1,b0_w13],[b0_w5,raw3,raw2,raw4,raw0,raw1,b0_w13],[b0_w6,raw3,raw1,raw4,raw0,raw2,b0_w13],[b0_w7,raw3,raw1,raw4,raw0,raw2,b0_w13],[b0_w77,raw3,raw4,raw0,raw2,raw1],[b0_w77,raw3,b0_w13,raw4,raw0,raw2,raw1],[b0_w31,raw3,raw4,raw0,raw2,raw1],[b0_w31,raw3,b0_w13,raw4,raw0,raw2,raw1],[b0_w8,raw4,raw0,raw3,raw2,raw1,b0_w13],[b0_w9,raw0,raw3,raw2,raw1,b0_w13],[b0_w9,raw4,raw0,raw3,raw2,raw1,b0_w13],[b0_w10,raw4,raw2,raw3,raw0,raw1,b0_w13],[b0_w11,raw2,raw3,raw0,raw1,b0_w13],[b0_w11,raw4,raw2,raw3,raw0,raw1,b0_w13],[b0_w12,raw1,raw3,raw0,raw2,b0_w13],[b0_w12,raw4,raw1,raw3,raw0,raw2,b0_w13],[b0_w14,raw0,raw2,raw3,raw4,raw1,b0_w13],[b0_w15,raw0,raw3,raw4,raw1,b0_w13],[b0_w15,raw0,raw2,raw3,raw4,raw1,b0_w13],[b0_w16,raw0,raw1,raw3,raw4,raw2,b0_w13],[b0_w17,raw0,raw3,raw4,raw2,b0_w13],[b0_w17,raw0,raw1,raw3,raw4,raw2,b0_w13],[b0_w78,raw0,raw3,raw4,raw2,raw1],[b0_w78,raw0,b0_w13,raw3,raw4,raw2,raw1],[b0_w65,raw0,raw3,raw4,raw2,raw1],[b0_w65,raw0,b0_w13,raw3,raw4,raw2,raw1],[b0_w18,raw2,raw1,raw3,raw4,raw0,b0_w13],[b0_w19,raw2,raw1,raw3,raw4,raw0,b0_w13],[b0_w79,raw3,raw4,raw0,raw1],[b0_w79,raw2,raw3,raw4,raw0,raw1],[b0_w79,b0_w13,raw3,raw4,raw0,raw1],[b0_w79,raw2,b0_w13,raw3,raw4,raw0,raw1],[b0_w73,raw2,raw3,raw4,raw0,raw1],[b0_w73,raw2,b0_w13,raw3,raw4,raw0,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead32
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead33
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead55
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead104
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead128
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead163
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead184
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead216
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead230
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead370
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead371
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead66
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead372
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead273
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead290
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead291
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead320
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead334
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead335
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead360
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead361
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead373
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead374
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead375
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead376
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead377
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead378
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead379
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead380
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead303
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead381
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead382
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead383
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead384
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead385
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead386
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead387
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead348
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead388
  · decide +kernel

def b0_s390 : List Sig := [b0_w33,b0_w14,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead390 : impossible 6 0 b0_s390 := by
  apply by_search
  decide +kernel

def b0_s391 : List Sig := [raw3,b0_w80,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead391 : impossible 6 0 b0_s391 := by
  apply by_search
  decide +kernel

def b0_s392 : List Sig := [b0_w14,raw3,b0_w80,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead392 : impossible 6 0 b0_s392 := by
  apply by_search
  decide +kernel

def b0_s393 : List Sig := [b0_w57,b0_w14,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead393 : impossible 6 0 b0_s393 := by
  apply by_search
  decide +kernel

def b0_s394 : List Sig := [raw3,raw4,b0_w81,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead394 : impossible 6 0 b0_s394 := by
  apply by_search
  decide +kernel

def b0_s395 : List Sig := [b0_w14,raw3,raw4,b0_w81,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead395 : impossible 6 0 b0_s395 := by
  apply by_search
  decide +kernel

def b0_s396 : List Sig := [b0_w82,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead396 : impossible 6 0 b0_s396 := by
  apply by_search
  decide +kernel

def b0_s397 : List Sig := [b0_w82,b0_w14,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead397 : impossible 6 0 b0_s397 := by
  apply by_search
  decide +kernel

def b0_s398 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w83]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead398 : impossible 6 0 b0_s398 := by
  apply by_search
  decide +kernel

def b0_s399 : List Sig := [b0_w14,raw3,raw4,raw0,raw2,raw1,b0_w83]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead399 : impossible 6 0 b0_s399 := by
  apply by_search
  decide +kernel

def b0_s400 : List Sig := [b0_w14,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead400 : impossible 6 0 b0_s400 := by
  apply by_search
  decide +kernel

def b0_s401 : List Sig := [b0_w14,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead401 : impossible 6 0 b0_s401 := by
  apply by_search
  decide +kernel

def b0_s402 : List Sig := [b0_w14,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead402 : impossible 6 0 b0_s402 := by
  apply by_search
  decide +kernel

def b0_s403 : List Sig := [b0_w14,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead403 : impossible 6 0 b0_s403 := by
  apply by_search
  decide +kernel

def b0_s404 : List Sig := [b0_w14,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead404 : impossible 6 0 b0_s404 := by
  apply by_search
  decide +kernel

def b0_s405 : List Sig := [b0_w14,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead405 : impossible 6 0 b0_s405 := by
  apply by_search
  decide +kernel

def b0_s389 : List Sig := [b0_w14,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead389 : impossible 7 0 b0_s389 := by
  apply reject_branch 6 0 b0_s389 [] [[b0_w33,raw3,raw4,raw0,raw2,raw1],[b0_w33,b0_w14,raw3,raw4,raw0,raw2,raw1],[b0_w80,raw3,raw4,raw0,raw2,raw1],[b0_w80,b0_w14,raw3,raw4,raw0,raw2,raw1],[b0_w57,raw4,raw3,raw0,raw2,raw1],[b0_w57,b0_w14,raw4,raw3,raw0,raw2,raw1],[b0_w81,raw4,raw3,raw0,raw2,raw1],[b0_w81,b0_w14,raw4,raw3,raw0,raw2,raw1],[b0_w82,raw1,raw3,raw4,raw0,raw2],[b0_w82,b0_w14,raw1,raw3,raw4,raw0,raw2],[b0_w83,raw1,raw3,raw4,raw0,raw2],[b0_w83,b0_w14,raw1,raw3,raw4,raw0,raw2],[b0_w0,raw3,raw4,b0_w14,raw0,raw2,raw1],[b0_w1,raw3,raw4,b0_w14,raw0,raw2,raw1],[b0_w2,raw3,raw0,b0_w14,raw4,raw2,raw1],[b0_w3,raw3,raw0,b0_w14,raw4,raw2,raw1],[b0_w4,raw3,raw2,b0_w14,raw4,raw0,raw1],[b0_w5,raw3,raw2,b0_w14,raw4,raw0,raw1],[b0_w6,raw3,raw1,b0_w14,raw4,raw0,raw2],[b0_w7,raw3,raw1,b0_w14,raw4,raw0,raw2],[b0_w8,raw4,raw0,b0_w14,raw3,raw2,raw1],[b0_w9,raw4,raw0,b0_w14,raw3,raw2,raw1],[b0_w10,raw4,raw2,b0_w14,raw3,raw0,raw1],[b0_w11,raw4,raw2,b0_w14,raw3,raw0,raw1],[b0_w12,raw4,raw1,b0_w14,raw3,raw0,raw2],[b0_w13,raw4,raw1,b0_w14,raw3,raw0,raw2],[b0_w15,raw0,b0_w14,raw3,raw4,raw1],[b0_w15,raw0,raw2,b0_w14,raw3,raw4,raw1],[b0_w16,raw0,raw1,b0_w14,raw3,raw4,raw2],[b0_w17,raw0,raw1,b0_w14,raw3,raw4,raw2],[b0_w18,raw2,raw1,b0_w14,raw3,raw4,raw0],[b0_w19,raw2,raw1,b0_w14,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead81
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead390
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead391
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead392
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead256
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead393
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead394
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead395
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead396
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead397
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead398
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead399
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead34
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead68
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead105
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead129
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead164
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead185
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead217
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead234
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead274
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead292
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead321
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead336
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead362
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead373
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead400
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead401
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead402
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead403
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead404
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead405
  · decide +kernel

def b0_s407 : List Sig := [b0_w84,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead407 : impossible 6 0 b0_s407 := by
  apply by_search
  decide +kernel

def b0_s408 : List Sig := [raw3,raw4,raw0,raw1,b0_w15,b0_w39]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead408 : impossible 6 0 b0_s408 := by
  apply by_search
  decide +kernel

def b0_s409 : List Sig := [b0_w85,raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead409 : impossible 6 0 b0_s409 := by
  apply by_search
  decide +kernel

def b0_s410 : List Sig := [raw3,raw4,raw0,raw1,b0_w15,b0_w63]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead410 : impossible 6 0 b0_s410 := by
  apply by_search
  decide +kernel

def b0_s411 : List Sig := [raw3,raw4,b0_w16,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead411 : impossible 6 0 b0_s411 := by
  apply by_search
  decide +kernel

def b0_s412 : List Sig := [raw3,raw4,raw1,b0_w17,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead412 : impossible 6 0 b0_s412 := by
  apply by_search
  decide +kernel

def b0_s413 : List Sig := [raw3,raw4,raw0,raw1,b0_w17,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead413 : impossible 6 0 b0_s413 := by
  apply by_search
  decide +kernel

def b0_s414 : List Sig := [raw3,raw4,raw0,b0_w86,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead414 : impossible 6 0 b0_s414 := by
  apply by_search
  decide +kernel

def b0_s415 : List Sig := [raw3,raw4,raw0,raw1,b0_w15,b0_w87]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead415 : impossible 6 0 b0_s415 := by
  apply by_search
  decide +kernel

def b0_s406 : List Sig := [raw3,raw4,raw0,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead406 : impossible 7 0 b0_s406 := by
  apply reject_branch 6 0 b0_s406 [] [[b0_w0,raw3,raw4,raw0,raw1,b0_w15],[b0_w1,raw3,raw4,raw0,raw1,b0_w15],[b0_w2,raw3,raw0,raw4,raw1,b0_w15],[b0_w3,raw3,raw0,raw4,raw1,b0_w15],[b0_w6,raw3,raw1,raw4,raw0,b0_w15],[b0_w7,raw3,raw1,raw4,raw0,b0_w15],[b0_w84,raw3,b0_w15,raw4,raw0,raw1],[b0_w39,raw3,b0_w15,raw4,raw0,raw1],[b0_w8,raw4,raw0,raw3,raw1,b0_w15],[b0_w9,raw4,raw0,raw3,raw1,b0_w15],[b0_w12,raw4,raw1,raw3,raw0,b0_w15],[b0_w13,raw4,raw1,raw3,raw0,b0_w15],[b0_w85,raw4,b0_w15,raw3,raw0,raw1],[b0_w63,raw4,b0_w15,raw3,raw0,raw1],[b0_w16,raw0,raw1,raw3,raw4,b0_w15],[b0_w17,raw1,raw3,raw4,b0_w15],[b0_w17,raw0,raw1,raw3,raw4,b0_w15],[b0_w86,raw1,b0_w15,raw3,raw4,raw0],[b0_w87,raw1,b0_w15,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead35
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead69
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead106
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead130
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead218
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead235
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead407
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead408
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead275
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead293
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead363
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead374
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead409
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead410
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead411
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead412
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead413
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead414
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead415
  · decide +kernel

def b0_s417 : List Sig := [b0_w84,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead417 : impossible 6 0 b0_s417 := by
  apply by_search
  decide +kernel

def b0_s418 : List Sig := [b0_w84,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead418 : impossible 6 0 b0_s418 := by
  apply by_search
  decide +kernel

def b0_s419 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w15,b0_w39]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead419 : impossible 6 0 b0_s419 := by
  apply by_search
  decide +kernel

def b0_s420 : List Sig := [b0_w85,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead420 : impossible 6 0 b0_s420 := by
  apply by_search
  decide +kernel

def b0_s421 : List Sig := [b0_w85,raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead421 : impossible 6 0 b0_s421 := by
  apply by_search
  decide +kernel

def b0_s422 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w15,b0_w63]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead422 : impossible 6 0 b0_s422 := by
  apply by_search
  decide +kernel

def b0_s423 : List Sig := [raw3,raw4,b0_w16,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead423 : impossible 6 0 b0_s423 := by
  apply by_search
  decide +kernel

def b0_s424 : List Sig := [raw3,raw4,raw2,raw1,b0_w17,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead424 : impossible 6 0 b0_s424 := by
  apply by_search
  decide +kernel

def b0_s425 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w17,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead425 : impossible 6 0 b0_s425 := by
  apply by_search
  decide +kernel

def b0_s426 : List Sig := [raw3,raw4,raw0,b0_w18,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead426 : impossible 6 0 b0_s426 := by
  apply by_search
  decide +kernel

def b0_s427 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead427 : impossible 6 0 b0_s427 := by
  apply by_search
  decide +kernel

def b0_s428 : List Sig := [raw3,raw4,raw0,raw1,b0_w15,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead428 : impossible 6 0 b0_s428 := by
  apply by_search
  decide +kernel

def b0_s429 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w15,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead429 : impossible 6 0 b0_s429 := by
  apply by_search
  decide +kernel

def b0_s430 : List Sig := [raw3,raw4,raw0,raw2,b0_w86,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead430 : impossible 6 0 b0_s430 := by
  apply by_search
  decide +kernel

def b0_s431 : List Sig := [raw3,raw4,raw0,raw2,b0_w86,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead431 : impossible 6 0 b0_s431 := by
  apply by_search
  decide +kernel

def b0_s432 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w87]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead432 : impossible 6 0 b0_s432 := by
  apply by_search
  decide +kernel

def b0_s433 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w15,b0_w87]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead433 : impossible 6 0 b0_s433 := by
  apply by_search
  decide +kernel

def b0_s416 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead416 : impossible 7 0 b0_s416 := by
  apply reject_branch 6 0 b0_s416 [] [[b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w15],[b0_w1,raw3,raw4,raw0,raw2,raw1,b0_w15],[b0_w2,raw3,raw0,raw4,raw2,raw1,b0_w15],[b0_w3,raw3,raw0,raw4,raw2,raw1,b0_w15],[b0_w4,raw3,raw4,raw0,raw1,b0_w15],[b0_w4,raw3,raw2,raw4,raw0,raw1,b0_w15],[b0_w5,raw3,raw4,raw0,raw1,b0_w15],[b0_w5,raw3,raw2,raw4,raw0,raw1,b0_w15],[b0_w6,raw3,raw1,raw4,raw0,raw2,b0_w15],[b0_w7,raw3,raw1,raw4,raw0,raw2,b0_w15],[b0_w84,raw3,raw4,raw0,raw2,raw1],[b0_w84,raw3,b0_w15,raw4,raw0,raw2,raw1],[b0_w39,raw3,raw4,raw0,raw2,raw1],[b0_w39,raw3,b0_w15,raw4,raw0,raw2,raw1],[b0_w8,raw4,raw0,raw3,raw2,raw1,b0_w15],[b0_w9,raw4,raw0,raw3,raw2,raw1,b0_w15],[b0_w10,raw4,raw3,raw0,raw1,b0_w15],[b0_w10,raw4,raw2,raw3,raw0,raw1,b0_w15],[b0_w11,raw4,raw3,raw0,raw1,b0_w15],[b0_w11,raw4,raw2,raw3,raw0,raw1,b0_w15],[b0_w12,raw4,raw1,raw3,raw0,raw2,b0_w15],[b0_w13,raw4,raw1,raw3,raw0,raw2,b0_w15],[b0_w85,raw4,raw3,raw0,raw2,raw1],[b0_w85,raw4,b0_w15,raw3,raw0,raw2,raw1],[b0_w63,raw4,raw3,raw0,raw2,raw1],[b0_w63,raw4,b0_w15,raw3,raw0,raw2,raw1],[b0_w14,raw0,raw3,raw4,raw1,b0_w15],[b0_w14,raw0,raw2,raw3,raw4,raw1,b0_w15],[b0_w16,raw0,raw1,raw3,raw4,raw2,b0_w15],[b0_w17,raw1,raw3,raw4,raw2,b0_w15],[b0_w17,raw0,raw1,raw3,raw4,raw2,b0_w15],[b0_w18,raw1,raw3,raw4,raw0,b0_w15],[b0_w18,raw2,raw1,raw3,raw4,raw0,b0_w15],[b0_w19,raw1,raw3,raw4,raw0,b0_w15],[b0_w19,raw2,raw1,raw3,raw4,raw0,b0_w15],[b0_w86,raw1,raw3,raw4,raw0,raw2],[b0_w86,raw1,b0_w15,raw3,raw4,raw0,raw2],[b0_w87,raw1,raw3,raw4,raw0,raw2],[b0_w87,raw1,b0_w15,raw3,raw4,raw0,raw2]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead36
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead70
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead107
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead131
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead165
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead166
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead186
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead187
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead219
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead236
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead417
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead418
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead136
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead419
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead276
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead294
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead322
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead323
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead337
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead338
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead364
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead375
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead420
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead421
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead299
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead422
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead400
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead401
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead423
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead424
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead425
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead426
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead427
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead428
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead429
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead430
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead431
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead432
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead433
  · decide +kernel

def b0_s435 : List Sig := [b0_w35,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead435 : impossible 6 0 b0_s435 := by
  apply by_search
  decide +kernel

def b0_s436 : List Sig := [raw4,raw0,b0_w88,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead436 : impossible 6 0 b0_s436 := by
  apply by_search
  decide +kernel

def b0_s437 : List Sig := [raw3,raw4,raw0,b0_w88,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead437 : impossible 6 0 b0_s437 := by
  apply by_search
  decide +kernel

def b0_s438 : List Sig := [raw4,b0_w16,raw0,b0_w88,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead438 : impossible 6 0 b0_s438 := by
  apply by_search
  decide +kernel

def b0_s439 : List Sig := [raw3,raw4,b0_w16,raw0,b0_w88,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead439 : impossible 6 0 b0_s439 := by
  apply by_search
  decide +kernel

def b0_s440 : List Sig := [b0_w59,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead440 : impossible 6 0 b0_s440 := by
  apply by_search
  decide +kernel

def b0_s441 : List Sig := [raw3,raw0,b0_w89,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead441 : impossible 6 0 b0_s441 := by
  apply by_search
  decide +kernel

def b0_s442 : List Sig := [raw3,raw4,raw0,b0_w89,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead442 : impossible 6 0 b0_s442 := by
  apply by_search
  decide +kernel

def b0_s443 : List Sig := [raw3,b0_w16,raw0,b0_w89,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead443 : impossible 6 0 b0_s443 := by
  apply by_search
  decide +kernel

def b0_s444 : List Sig := [raw3,raw4,b0_w16,raw0,b0_w89,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead444 : impossible 6 0 b0_s444 := by
  apply by_search
  decide +kernel

def b0_s445 : List Sig := [b0_w82,raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead445 : impossible 6 0 b0_s445 := by
  apply by_search
  decide +kernel

def b0_s446 : List Sig := [raw3,raw4,raw0,raw1,b0_w90]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead446 : impossible 6 0 b0_s446 := by
  apply by_search
  decide +kernel

def b0_s447 : List Sig := [raw3,raw4,b0_w16,raw0,raw1,b0_w90]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead447 : impossible 6 0 b0_s447 := by
  apply by_search
  decide +kernel

def b0_s448 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w90]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead448 : impossible 6 0 b0_s448 := by
  apply by_search
  decide +kernel

def b0_s449 : List Sig := [raw3,raw4,b0_w16,raw0,raw2,raw1,b0_w90]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead449 : impossible 6 0 b0_s449 := by
  apply by_search
  decide +kernel

def b0_s450 : List Sig := [raw3,raw4,b0_w16,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead450 : impossible 6 0 b0_s450 := by
  apply by_search
  decide +kernel

def b0_s451 : List Sig := [raw3,raw4,b0_w16,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead451 : impossible 6 0 b0_s451 := by
  apply by_search
  decide +kernel

def b0_s452 : List Sig := [raw3,raw4,b0_w16,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead452 : impossible 6 0 b0_s452 := by
  apply by_search
  decide +kernel

def b0_s434 : List Sig := [raw3,raw4,b0_w16,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead434 : impossible 7 0 b0_s434 := by
  apply reject_branch 6 0 b0_s434 [] [[b0_w0,raw3,raw4,b0_w16,raw0,raw2,raw1],[b0_w1,raw3,raw4,b0_w16,raw0,raw2,raw1],[b0_w35,raw3,raw4,raw0,raw2,raw1],[b0_w35,raw3,b0_w16,raw4,raw0,raw2,raw1],[b0_w88,raw4,raw0,raw2,raw1],[b0_w88,raw3,raw4,raw0,raw2,raw1],[b0_w88,b0_w16,raw4,raw0,raw2,raw1],[b0_w88,raw3,b0_w16,raw4,raw0,raw2,raw1],[b0_w2,raw3,raw0,raw4,b0_w16,raw2,raw1],[b0_w3,raw3,raw0,raw4,b0_w16,raw2,raw1],[b0_w4,raw3,raw2,raw4,b0_w16,raw0,raw1],[b0_w5,raw3,raw2,raw4,b0_w16,raw0,raw1],[b0_w6,raw3,raw1,raw4,b0_w16,raw0,raw2],[b0_w7,raw3,raw1,raw4,b0_w16,raw0,raw2],[b0_w59,raw4,raw3,raw0,raw2,raw1],[b0_w59,raw4,b0_w16,raw3,raw0,raw2,raw1],[b0_w89,raw3,raw0,raw2,raw1],[b0_w89,raw4,raw3,raw0,raw2,raw1],[b0_w89,b0_w16,raw3,raw0,raw2,raw1],[b0_w89,raw4,b0_w16,raw3,raw0,raw2,raw1],[b0_w8,raw4,raw0,raw3,b0_w16,raw2,raw1],[b0_w9,raw4,raw0,raw3,b0_w16,raw2,raw1],[b0_w10,raw4,raw2,raw3,b0_w16,raw0,raw1],[b0_w11,raw4,raw2,raw3,b0_w16,raw0,raw1],[b0_w12,raw4,raw1,raw3,b0_w16,raw0,raw2],[b0_w13,raw4,raw1,raw3,b0_w16,raw0,raw2],[b0_w82,raw2,raw3,raw4,raw0,raw1],[b0_w82,b0_w16,raw2,raw3,raw4,raw0,raw1],[b0_w90,raw3,raw4,raw0,raw1],[b0_w90,b0_w16,raw3,raw4,raw0,raw1],[b0_w90,raw2,raw3,raw4,raw0,raw1],[b0_w90,b0_w16,raw2,raw3,raw4,raw0,raw1],[b0_w14,raw0,raw2,raw3,raw4,b0_w16,raw1],[b0_w15,raw0,raw3,raw4,b0_w16,raw1],[b0_w15,raw0,raw2,raw3,raw4,b0_w16,raw1],[b0_w17,raw0,raw1,raw3,raw4,b0_w16,raw2],[b0_w18,raw2,raw1,raw3,raw4,b0_w16,raw0],[b0_w19,raw2,raw1,raw3,raw4,b0_w16,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead37
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead71
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead87
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead435
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead436
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead437
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead438
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead439
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead108
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead132
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead167
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead191
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead220
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead237
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead262
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead440
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead441
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead442
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead443
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead444
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead277
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead295
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead324
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead342
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead365
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead376
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead396
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead445
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead446
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead447
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead448
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead449
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead402
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead411
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead423
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead450
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead451
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead452
  · decide +kernel

def b0_s454 : List Sig := [b0_w91,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead454 : impossible 6 0 b0_s454 := by
  apply by_search
  decide +kernel

def b0_s455 : List Sig := [b0_w91,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead455 : impossible 6 0 b0_s455 := by
  apply by_search
  decide +kernel

def b0_s456 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w17,b0_w41]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead456 : impossible 6 0 b0_s456 := by
  apply by_search
  decide +kernel

def b0_s457 : List Sig := [b0_w92,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead457 : impossible 6 0 b0_s457 := by
  apply by_search
  decide +kernel

def b0_s458 : List Sig := [b0_w92,raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead458 : impossible 6 0 b0_s458 := by
  apply by_search
  decide +kernel

def b0_s459 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w17,b0_w65]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead459 : impossible 6 0 b0_s459 := by
  apply by_search
  decide +kernel

def b0_s460 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead460 : impossible 6 0 b0_s460 := by
  apply by_search
  decide +kernel

def b0_s461 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w17,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead461 : impossible 6 0 b0_s461 := by
  apply by_search
  decide +kernel

def b0_s462 : List Sig := [raw3,raw4,raw0,b0_w93,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead462 : impossible 6 0 b0_s462 := by
  apply by_search
  decide +kernel

def b0_s463 : List Sig := [raw3,raw4,raw0,b0_w93,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead463 : impossible 6 0 b0_s463 := by
  apply by_search
  decide +kernel

def b0_s464 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w17,b0_w87]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead464 : impossible 6 0 b0_s464 := by
  apply by_search
  decide +kernel

def b0_s453 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead453 : impossible 7 0 b0_s453 := by
  apply reject_branch 6 0 b0_s453 [] [[b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w17],[b0_w1,raw3,raw4,raw0,raw2,raw1,b0_w17],[b0_w2,raw3,raw0,raw4,raw2,raw1,b0_w17],[b0_w3,raw3,raw0,raw4,raw2,raw1,b0_w17],[b0_w4,raw3,raw2,raw4,raw0,raw1,b0_w17],[b0_w5,raw3,raw2,raw4,raw0,raw1,b0_w17],[b0_w6,raw3,raw1,raw4,raw0,raw2,b0_w17],[b0_w7,raw3,raw4,raw0,raw2,b0_w17],[b0_w7,raw3,raw1,raw4,raw0,raw2,b0_w17],[b0_w91,raw3,raw4,raw0,raw2,raw1],[b0_w91,raw3,b0_w17,raw4,raw0,raw2,raw1],[b0_w41,raw3,raw4,raw0,raw2,raw1],[b0_w41,raw3,b0_w17,raw4,raw0,raw2,raw1],[b0_w8,raw4,raw0,raw3,raw2,raw1,b0_w17],[b0_w9,raw4,raw0,raw3,raw2,raw1,b0_w17],[b0_w10,raw4,raw2,raw3,raw0,raw1,b0_w17],[b0_w11,raw4,raw2,raw3,raw0,raw1,b0_w17],[b0_w12,raw4,raw1,raw3,raw0,raw2,b0_w17],[b0_w13,raw4,raw3,raw0,raw2,b0_w17],[b0_w13,raw4,raw1,raw3,raw0,raw2,b0_w17],[b0_w92,raw4,raw3,raw0,raw2,raw1],[b0_w92,raw4,b0_w17,raw3,raw0,raw2,raw1],[b0_w65,raw4,raw3,raw0,raw2,raw1],[b0_w65,raw4,b0_w17,raw3,raw0,raw2,raw1],[b0_w14,raw0,raw2,raw3,raw4,raw1,b0_w17],[b0_w15,raw3,raw4,raw1,b0_w17],[b0_w15,raw0,raw3,raw4,raw1,b0_w17],[b0_w15,raw2,raw3,raw4,raw1,b0_w17],[b0_w15,raw0,raw2,raw3,raw4,raw1,b0_w17],[b0_w16,raw0,raw1,raw3,raw4,raw2,b0_w17],[b0_w18,raw2,raw1,raw3,raw4,raw0,b0_w17],[b0_w19,raw2,raw1,raw3,raw4,raw0,b0_w17],[b0_w93,raw2,raw3,raw4,raw0,raw1],[b0_w93,raw2,b0_w17,raw3,raw4,raw0,raw1],[b0_w87,raw2,raw3,raw4,raw0,raw1],[b0_w87,raw2,b0_w17,raw3,raw4,raw0,raw1]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead38
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead72
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead109
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead133
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead168
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead192
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead221
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead238
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead239
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead454
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead455
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead140
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead456
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead278
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead296
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead325
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead343
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead366
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead377
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead378
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead457
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead458
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead303
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead459
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead403
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead412
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead413
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead424
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead425
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead450
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead460
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead461
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead462
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead463
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead432
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead464
  · decide +kernel

def b0_s466 : List Sig := [b0_w44,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead466 : impossible 6 0 b0_s466 := by
  apply by_search
  decide +kernel

def b0_s467 : List Sig := [raw4,raw0,raw2,b0_w94,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead467 : impossible 6 0 b0_s467 := by
  apply by_search
  decide +kernel

def b0_s468 : List Sig := [raw3,raw4,raw0,raw2,b0_w94,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead468 : impossible 6 0 b0_s468 := by
  apply by_search
  decide +kernel

def b0_s469 : List Sig := [raw4,raw0,b0_w18,raw2,b0_w94,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead469 : impossible 6 0 b0_s469 := by
  apply by_search
  decide +kernel

def b0_s470 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,b0_w94,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead470 : impossible 6 0 b0_s470 := by
  apply by_search
  decide +kernel

def b0_s471 : List Sig := [b0_w68,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead471 : impossible 6 0 b0_s471 := by
  apply by_search
  decide +kernel

def b0_s472 : List Sig := [raw3,raw0,raw2,b0_w95,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead472 : impossible 6 0 b0_s472 := by
  apply by_search
  decide +kernel

def b0_s473 : List Sig := [raw3,raw4,raw0,raw2,b0_w95,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead473 : impossible 6 0 b0_s473 := by
  apply by_search
  decide +kernel

def b0_s474 : List Sig := [raw3,raw0,b0_w18,raw2,b0_w95,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead474 : impossible 6 0 b0_s474 := by
  apply by_search
  decide +kernel

def b0_s475 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,b0_w95,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead475 : impossible 6 0 b0_s475 := by
  apply by_search
  decide +kernel

def b0_s476 : List Sig := [b0_w82,raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead476 : impossible 6 0 b0_s476 := by
  apply by_search
  decide +kernel

def b0_s477 : List Sig := [raw3,raw4,raw2,raw1,b0_w96]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead477 : impossible 6 0 b0_s477 := by
  apply by_search
  decide +kernel

def b0_s478 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w96]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead478 : impossible 6 0 b0_s478 := by
  apply by_search
  decide +kernel

def b0_s479 : List Sig := [raw3,raw4,b0_w18,raw2,raw1,b0_w96]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead479 : impossible 6 0 b0_s479 := by
  apply by_search
  decide +kernel

def b0_s480 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,raw1,b0_w96]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead480 : impossible 6 0 b0_s480 := by
  apply by_search
  decide +kernel

def b0_s481 : List Sig := [raw3,raw4,raw0,b0_w18,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead481 : impossible 6 0 b0_s481 := by
  apply by_search
  decide +kernel

def b0_s482 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead482 : impossible 6 0 b0_s482 := by
  apply by_search
  decide +kernel

def b0_s465 : List Sig := [raw3,raw4,raw0,b0_w18,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead465 : impossible 7 0 b0_s465 := by
  apply reject_branch 6 0 b0_s465 [] [[b0_w0,raw3,raw4,raw0,b0_w18,raw2,raw1],[b0_w1,raw3,raw4,raw0,b0_w18,raw2,raw1],[b0_w2,raw3,raw0,raw4,b0_w18,raw2,raw1],[b0_w3,raw3,raw0,raw4,b0_w18,raw2,raw1],[b0_w44,raw3,raw4,raw0,raw2,raw1],[b0_w44,raw3,b0_w18,raw4,raw0,raw2,raw1],[b0_w94,raw4,raw0,raw2,raw1],[b0_w94,raw3,raw4,raw0,raw2,raw1],[b0_w94,b0_w18,raw4,raw0,raw2,raw1],[b0_w94,raw3,b0_w18,raw4,raw0,raw2,raw1],[b0_w4,raw3,raw4,raw0,b0_w18,raw1],[b0_w4,raw3,raw2,raw4,raw0,b0_w18,raw1],[b0_w5,raw3,raw2,raw4,raw0,b0_w18,raw1],[b0_w6,raw3,raw1,raw4,raw0,b0_w18,raw2],[b0_w7,raw3,raw1,raw4,raw0,b0_w18,raw2],[b0_w8,raw4,raw0,raw3,b0_w18,raw2,raw1],[b0_w9,raw4,raw0,raw3,b0_w18,raw2,raw1],[b0_w68,raw4,raw3,raw0,raw2,raw1],[b0_w68,raw4,b0_w18,raw3,raw0,raw2,raw1],[b0_w95,raw3,raw0,raw2,raw1],[b0_w95,raw4,raw3,raw0,raw2,raw1],[b0_w95,b0_w18,raw3,raw0,raw2,raw1],[b0_w95,raw4,b0_w18,raw3,raw0,raw2,raw1],[b0_w10,raw4,raw3,raw0,b0_w18,raw1],[b0_w10,raw4,raw2,raw3,raw0,b0_w18,raw1],[b0_w11,raw4,raw2,raw3,raw0,b0_w18,raw1],[b0_w12,raw4,raw1,raw3,raw0,b0_w18,raw2],[b0_w13,raw4,raw1,raw3,raw0,b0_w18,raw2],[b0_w82,raw0,raw3,raw4,raw2,raw1],[b0_w82,raw0,b0_w18,raw3,raw4,raw2,raw1],[b0_w96,raw3,raw4,raw2,raw1],[b0_w96,raw0,raw3,raw4,raw2,raw1],[b0_w96,b0_w18,raw3,raw4,raw2,raw1],[b0_w96,raw0,b0_w18,raw3,raw4,raw2,raw1],[b0_w14,raw0,raw2,raw3,raw4,b0_w18,raw1],[b0_w15,raw0,raw3,raw4,b0_w18,raw1],[b0_w15,raw0,raw2,raw3,raw4,b0_w18,raw1],[b0_w16,raw0,raw1,raw3,raw4,b0_w18,raw2],[b0_w17,raw0,raw1,raw3,raw4,b0_w18,raw2],[b0_w19,raw1,raw3,raw4,raw0,b0_w18],[b0_w19,raw2,raw1,raw3,raw4,raw0,b0_w18]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead39
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead73
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead110
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead142
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead151
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead466
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead467
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead468
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead469
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead470
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead169
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead170
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead193
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead222
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead243
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead279
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead305
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead314
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead471
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead472
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead473
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead474
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead475
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead326
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead327
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead344
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead367
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead382
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead396
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead476
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead477
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead478
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead479
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead480
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead404
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead426
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead427
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead451
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead460
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead481
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead482
  · decide +kernel

def b0_s484 : List Sig := [b0_w97,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead484 : impossible 6 0 b0_s484 := by
  apply by_search
  decide +kernel

def b0_s485 : List Sig := [b0_w97,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead485 : impossible 6 0 b0_s485 := by
  apply by_search
  decide +kernel

def b0_s486 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w19,b0_w49]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead486 : impossible 6 0 b0_s486 := by
  apply by_search
  decide +kernel

def b0_s487 : List Sig := [b0_w98,raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead487 : impossible 6 0 b0_s487 := by
  apply by_search
  decide +kernel

def b0_s488 : List Sig := [b0_w98,raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead488 : impossible 6 0 b0_s488 := by
  apply by_search
  decide +kernel

def b0_s489 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w19,b0_w73]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead489 : impossible 6 0 b0_s489 := by
  apply by_search
  decide +kernel

def b0_s490 : List Sig := [raw3,raw4,b0_w99,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead490 : impossible 6 0 b0_s490 := by
  apply by_search
  decide +kernel

def b0_s491 : List Sig := [raw3,raw4,b0_w99,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead491 : impossible 6 0 b0_s491 := by
  apply by_search
  decide +kernel

def b0_s492 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w19,b0_w87]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead492 : impossible 6 0 b0_s492 := by
  apply by_search
  decide +kernel

def b0_s483 : List Sig := [raw3,raw4,raw0,raw2,raw1,b0_w19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead483 : impossible 7 0 b0_s483 := by
  apply reject_branch 6 0 b0_s483 [] [[b0_w0,raw3,raw4,raw0,raw2,raw1,b0_w19],[b0_w1,raw3,raw4,raw0,raw2,raw1,b0_w19],[b0_w2,raw3,raw0,raw4,raw2,raw1,b0_w19],[b0_w3,raw3,raw0,raw4,raw2,raw1,b0_w19],[b0_w4,raw3,raw2,raw4,raw0,raw1,b0_w19],[b0_w5,raw3,raw2,raw4,raw0,raw1,b0_w19],[b0_w6,raw3,raw1,raw4,raw0,raw2,b0_w19],[b0_w7,raw3,raw1,raw4,raw0,raw2,b0_w19],[b0_w97,raw3,raw4,raw0,raw2,raw1],[b0_w97,raw3,b0_w19,raw4,raw0,raw2,raw1],[b0_w49,raw3,raw4,raw0,raw2,raw1],[b0_w49,raw3,b0_w19,raw4,raw0,raw2,raw1],[b0_w8,raw4,raw0,raw3,raw2,raw1,b0_w19],[b0_w9,raw4,raw0,raw3,raw2,raw1,b0_w19],[b0_w10,raw4,raw2,raw3,raw0,raw1,b0_w19],[b0_w11,raw4,raw2,raw3,raw0,raw1,b0_w19],[b0_w12,raw4,raw1,raw3,raw0,raw2,b0_w19],[b0_w13,raw4,raw1,raw3,raw0,raw2,b0_w19],[b0_w98,raw4,raw3,raw0,raw2,raw1],[b0_w98,raw4,b0_w19,raw3,raw0,raw2,raw1],[b0_w73,raw4,raw3,raw0,raw2,raw1],[b0_w73,raw4,b0_w19,raw3,raw0,raw2,raw1],[b0_w14,raw0,raw2,raw3,raw4,raw1,b0_w19],[b0_w15,raw0,raw3,raw4,raw1,b0_w19],[b0_w15,raw0,raw2,raw3,raw4,raw1,b0_w19],[b0_w16,raw0,raw1,raw3,raw4,raw2,b0_w19],[b0_w17,raw0,raw1,raw3,raw4,raw2,b0_w19],[b0_w99,raw0,raw3,raw4,raw2,raw1],[b0_w99,raw0,b0_w19,raw3,raw4,raw2,raw1],[b0_w87,raw0,raw3,raw4,raw2,raw1],[b0_w87,raw0,b0_w19,raw3,raw4,raw2,raw1],[b0_w18,raw1,raw3,raw4,raw0,b0_w19],[b0_w18,raw2,raw1,raw3,raw4,raw0,b0_w19]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead40
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead74
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead111
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead143
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead171
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead194
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead223
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead244
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead484
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead485
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead197
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead486
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead280
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead306
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead328
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead345
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead368
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead383
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead487
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead488
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead348
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead489
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead405
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead428
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead429
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead452
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead461
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead490
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead491
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead432
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead492
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead481
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead482
  · decide +kernel

def b0_s0 : List Sig := [raw3,raw4,raw0,raw2,raw1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0_dead0 : impossible 8 0 b0_s0 := by
  apply reject_branch 7 0 b0_s0 [] [[b0_w0,raw3,raw4,raw0,raw2,raw1],[b0_w1,raw3,raw4,raw0,raw2,raw1],[b0_w2,raw3,raw0,raw4,raw2,raw1],[b0_w3,raw3,raw0,raw4,raw2,raw1],[b0_w4,raw3,raw2,raw4,raw0,raw1],[b0_w5,raw3,raw2,raw4,raw0,raw1],[b0_w6,raw3,raw1,raw4,raw0,raw2],[b0_w7,raw3,raw1,raw4,raw0,raw2],[b0_w8,raw4,raw0,raw3,raw2,raw1],[b0_w9,raw4,raw0,raw3,raw2,raw1],[b0_w10,raw4,raw2,raw3,raw0,raw1],[b0_w11,raw4,raw2,raw3,raw0,raw1],[b0_w12,raw4,raw1,raw3,raw0,raw2],[b0_w13,raw4,raw1,raw3,raw0,raw2],[b0_w14,raw0,raw2,raw3,raw4,raw1],[b0_w15,raw0,raw3,raw4,raw1],[b0_w15,raw0,raw2,raw3,raw4,raw1],[b0_w16,raw0,raw1,raw3,raw4,raw2],[b0_w17,raw0,raw1,raw3,raw4,raw2],[b0_w18,raw2,raw1,raw3,raw4,raw0],[b0_w19,raw2,raw1,raw3,raw4,raw0]]
  · intro w hw; simp at hw
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead1
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead41
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead75
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead112
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead144
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead172
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead199
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead224
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead250
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead281
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead307
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead329
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead350
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead369
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead389
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead406
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead416
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead434
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead453
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead465
    · exact impossible_same (by decide +kernel) (by decide +kernel) b0_dead483
  · decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem branch_exclude_0 : impossible 8 0 raw :=
  impossible_same (by decide +kernel) (by decide +kernel) b0_dead0

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    9 ≤ C.size := by
  by_contra! hc
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length = 5 := rfl
  change C.gates.length < 9 at hc
  have hk8 : k ≤ 8 := by omega
  have ht4 : t ≤ 4 := by omega
  have no : impossible 8 t raw := by
    interval_cases t
    · exact branch_exclude_0
    · exact by_search exclude_1
    · exact by_search exclude_2
    · exact by_search exclude_3
    · exact by_search exclude_4
  exact no ht hk8 raw_nd eq

def upperGates : List Gate := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 12]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 9 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 13⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case8

namespace Case9

def raw0 : Sig := (0xffffff000fff000fff000ffffff000ffffffffffff000ffffff000fff000fff,0xa04a04a04a04a04a04a04a04a04a04a04a04a04a04a04a04a04a04a04a04a04a)
def raw1 : Sig := (0xf000ffffff000000ffffff000ffffff000fff000ffffff000ffffffffffff000,0xc20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c)
def raw2 : Sig := (0xffffffffffffffff000000000fffffffff000000fffffffff000000fffffffff,0x490490490490490490490490490490490490490490490490490490490490490)
def raw3 : Sig := (0xfffffffffffffffffffff000000000000000fffffffffffffff000000000,0x8e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e08e0)
def raw4 : Sig := (0xffffffffffffffffffffffffffffffffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4]

def sample (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfeeaece0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 256), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 7)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 3, search 7 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=5 := rfl
  change C.gates.length ≤ 7 at hc
  exact ⟨t,by omega,search_complete ht 7 (by omega) raw raw_nd eq⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_0 : search 7 0 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_1 : search 7 1 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_2 : search 7 2 raw = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem exclude_3 : search 7 3 raw = false := by decide +kernel

theorem lower (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = edgeF x) :
    8 ≤ C.size := by
  by_contra! hc
  obtain ⟨t, ht, hh⟩ := circuit_search C (by omega) h he
  interval_cases t

  · rw [exclude_0] at hh; contradiction
  · rw [exclude_1] at hh; contradiction
  · rw [exclude_2] at hh; contradiction
  · rw [exclude_3] at hh; contradiction

def upperGates : List Gate := [⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [10, 11]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem upper_data :
    (∀ g ∈ upperGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    upperGates.length = 8 ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨upperGates, 12⟩ (List.ofFn x) = edgeF x := by
  refine ⟨by simp [upperGates], rfl, ?_⟩
  decide +kernel

end Case9

end PEqualNP.Outside.L_meta_1441_aux

open PEqualNP.Outside.L_meta_1441_aux in

theorem PEqualNP.Outside.L_meta_1441 : ∀ T ∈ ({0xfeeaeac0, 0xeeeaeaaa, 0xeeeaeae8, 0xeeeaece8, 0xeeeaeee0, 0xfee8eae8, 0xfee8eee0, 0xfeeaeaa8, 0xfeeaeac8, 0xfeeaece0} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gates o hg _hnot he
  have hf : PEqualNP.MetaComplexity.FanInTwo ⟨gates, o⟩ := by
    intro g hm
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg g hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hlow := Case0.lower ⟨gates, o⟩ hf he
    refine ⟨Case0.upperGates, 12, Case0.upper_data.1, ?_, Case0.upper_data.2.2⟩
    rw [Case0.upper_data.2.1]
    exact hlow
  · have hlow := Case1.lower ⟨gates, o⟩ hf he
    refine ⟨Case1.upperGates, 10, Case1.upper_data.1, ?_, Case1.upper_data.2.2⟩
    rw [Case1.upper_data.2.1]
    exact hlow
  · have hlow := Case2.lower ⟨gates, o⟩ hf he
    refine ⟨Case2.upperGates, 12, Case2.upper_data.1, ?_, Case2.upper_data.2.2⟩
    rw [Case2.upper_data.2.1]
    exact hlow
  · have hlow := Case3.lower ⟨gates, o⟩ hf he
    refine ⟨Case3.upperGates, 10, Case3.upper_data.1, ?_, Case3.upper_data.2.2⟩
    rw [Case3.upper_data.2.1]
    exact hlow
  · have hlow := Case4.lower ⟨gates, o⟩ hf he
    refine ⟨Case4.upperGates, 9, Case4.upper_data.1, ?_, Case4.upper_data.2.2⟩
    rw [Case4.upper_data.2.1]
    exact hlow
  · have hlow := Case5.lower ⟨gates, o⟩ hf he
    refine ⟨Case5.upperGates, 12, Case5.upper_data.1, ?_, Case5.upper_data.2.2⟩
    rw [Case5.upper_data.2.1]
    exact hlow
  · have hlow := Case6.lower ⟨gates, o⟩ hf he
    refine ⟨Case6.upperGates, 12, Case6.upper_data.1, ?_, Case6.upper_data.2.2⟩
    rw [Case6.upper_data.2.1]
    exact hlow
  · have hlow := Case7.lower ⟨gates, o⟩ hf he
    refine ⟨Case7.upperGates, 13, Case7.upper_data.1, ?_, Case7.upper_data.2.2⟩
    rw [Case7.upper_data.2.1]
    exact hlow
  · have hlow := Case8.lower ⟨gates, o⟩ hf he
    refine ⟨Case8.upperGates, 13, Case8.upper_data.1, ?_, Case8.upper_data.2.2⟩
    rw [Case8.upper_data.2.1]
    exact hlow
  · have hlow := Case9.lower ⟨gates, o⟩ hf he
    refine ⟨Case9.upperGates, 12, Case9.upper_data.1, ?_, Case9.upper_data.2.2⟩
    rw [Case9.upper_data.2.1]
    exact hlow
