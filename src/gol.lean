import cautomaton utils data.nat.basic 

open utils

namespace gol
 
section gol

open list function

inductive cellT | A | D

open cellT

def cellT_str : cellT → string
  | A := "X"
  | D := " "

instance cellT_to_str : has_to_string cellT := ⟨cellT_str⟩

instance cellT_repr : has_repr cellT := ⟨cellT_str⟩

instance cellT_deceq : decidable_eq cellT :=
	λl r,
		begin
			cases l; cases r; try {exact is_true rfl}; apply is_false; trivial
		end

instance : has_coe cellT bool := ⟨λx, x = A⟩

instance coe_back : has_coe bool cellT := ⟨λx, if x then A else D⟩

def step (cell : cellT) (alive_neighbours : ℕ) : cellT :=
  if cell then
    if alive_neighbours < 2 then D else
    if bor (alive_neighbours = 2) (alive_neighbours = 3) then A
    else D
  else
    if alive_neighbours = 3 then A
    else D

def gol_step (cell : cellT) (neigh : list cellT) :=
  step cell (count_at_single neigh tt)

end gol

open cellT

attribute [reducible]
def gol := cautomaton cellT

def mk_gol (g : agrid₀ cellT) : gol :=
  ⟨g, D, cautomatons.moore, gol_step, cautomatons.ext_one⟩

def empty := fgrid.mk 2 2 dec_trivial ⟨0, 1⟩ (λx y, D)

def empty_g :=
  agrid₀.mk ⟨2, 2, dec_trivial, ⟨[D, D, D, D], rfl⟩⟩ ⟨0, 1⟩ 

def empty_aut : gol := mk_gol empty

def empty_aut_g : gol := mk_gol empty_g

def row := fgrid.mk 1 3 dec_trivial ⟨-1, 0⟩ (λx y, A)

def row_gol : gol := mk_gol row

def col := agrid₀.mk ⟨3, 1, dec_trivial, ⟨[A, A, A], rfl⟩⟩ ⟨0, 1⟩

def col_gol : gol := mk_gol col

def box := fgrid.mk 2 2 dec_trivial ⟨0, 1⟩ (λx y, A)

def box_gol : gol := mk_gol box

def dies := agrid₀.mk ⟨3, 2, dec_trivial, ⟨[A, D, A, D, D, A], rfl⟩⟩ ⟨0, 1⟩

def dies_gol : gol := mk_gol dies

private lemma col_even {n} (h : n % 2 = 0) {a} {g} 
  (h₂ : a = mk_gol g)
  (h₃ : a = col_gol) : step_n a n = a :=
begin
  unfold step_n,
  rw @periode_cycle _ _ _ _ 2 dec_trivial,
    {
      rw [h, iterate_zero]
    },
    {
      rw h₂, subst h₃,
      rw caut_eq_iff; try { by simp },
      rw ← h₂, refl
    }
end

lemma col_gol_even {n} (h : n % 2 = 0) : step_n col_gol n = col_gol :=
  col_even h rfl rfl

private lemma col_row {n} (h : n % 2 = 1) {a} {g} 
  (h₂ : a = mk_gol g)
  (h₃ : a = col_gol) : step_n a n = row_gol :=
begin
  unfold step_n,
  rw @periode_cycle _ _ _ _ 2 dec_trivial,
    {
      rw h, rw iterate_one,
      rw iterate_zero, rw h₃,
      rw caut_eq_iff; try { by simp [col_gol, row_gol, mk_gol] },
      refl
    },
    {
      rw h₃, refl
    }
end

lemma col_row_odd {n} (h : n % 2 = 1) : step_n col_gol n = row_gol :=
  col_row h rfl rfl

open list prod

def find_period (max : ℕ) (a : gol) : option ℕ :=
  let incr_iota := list.reverse $ list.iota max in
  prod.snd <$> list.find ((=tt) ∘ prod.fst) (
    list.zip (list.map ((=a.g) ∘ cautomaton.g ∘ (step_n a)) incr_iota) incr_iota
  ) 

meta def solve_periodic_gol_n (n : ℕ) : tactic unit :=
  do {
    `(periodic %%a) ← tactic.target,
    t ← tactic.infer_type a,
    aut ← tactic.eval_expr (cautomaton _) a,
    let val := find_period n aut in do
      v ← val,
      tactic.existsi `(v),
      tactic.split,
      tactic.exact_dec_trivial,
      tactic.reflexivity
  } <|> tactic.fail
        "Unable to discover periodicity. Try to increase the depth of search."

meta def periodic_aut : tactic unit := solve_periodic_gol_n 16

example : periodic col_gol := ⟨2, ⟨dec_trivial, rfl⟩⟩

example : periodic col_gol := by periodic_aut

end gol