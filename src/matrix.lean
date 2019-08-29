import grid utils data.vector2 tactic.elide

open utils

namespace matrix

structure matrix (m n : ℕ) (α : Type) :=
  (g  : vec_grid₀ α)
  (hr : g.r = m)
  (hc : g.c = n)

section ext

variables {m n : ℕ} {α : Type} {m₁ m₂ : matrix m n α}

theorem ext_iff : m₁.g = m₂.g ↔ m₁ = m₂ :=
  by cases m₁; rcases m₂; simp

@[extensionality] theorem ext : m₁.g = m₂.g → m₁ = m₂ := ext_iff.1

end ext

section operations

variables {m n o p : ℕ} {α β γ δ : Type}

open relative_grid grid

lemma matrix_unempty {m₁ : matrix m n α} : m * n > 0 :=
  by rcases m₁ with ⟨⟨⟨_, _, _, _⟩, _⟩, _, _⟩; finish

def matrix_string [has_to_string α] (m : matrix m n α) :=
  grid_str m.g

instance matrix_repr [has_to_string α] : has_repr (matrix m n α) :=
  ⟨matrix_string⟩

instance matrix_to_string [has_to_string α] : has_to_string (matrix m n α) :=
  ⟨matrix_string⟩

instance matrix_functor : functor (matrix m n) := {
  map := λα β f m,
    ⟨f <$> m.g, by rw [vec_grid₀_fmap_r, m.hr], by rw [vec_grid₀_fmap_c, m.hc]⟩
}

instance matrix_functor_law : is_lawful_functor (matrix m n) := {
  id_map := λα ⟨⟨⟨r, c, h, d⟩, o⟩, hr, hc⟩, by simp [(<$>), vector.map_id],
  comp_map := λα β γ f h ⟨⟨⟨r, c, h, d⟩, o⟩, hr, hc⟩, by simp [(<$>)]
}

def m₁ : matrix 5 2 ℕ :=
  matrix.mk
    (vec_grid₀.mk ⟨5, 2, dec_trivial, ⟨[1, 3, 4, 5, 7, 8, 9, 10, 11, 12], dec_trivial⟩⟩ ⟨5, 1⟩)
    rfl rfl

def m₂ : matrix 2 3 ℕ :=
  matrix.mk
    (vec_grid₀.mk ⟨2, 3, dec_trivial, ⟨[2, 2, 2, 2, 2, 2], dec_trivial⟩⟩ ⟨0, 0⟩)
    rfl rfl

instance [has_add α] : has_add (matrix m n α) := {
  add := λm₁ m₂,
    ⟨⟨⟨m, n, @matrix_unempty _ _ _ m₁,
      begin
        rcases m₁ with ⟨⟨⟨g₁r, g₁c, g₁h, g₁d⟩, g₁o⟩, hr₁, hc₁⟩,
        rcases m₂ with ⟨⟨⟨g₂r, g₂c, g₂h, g₂d⟩, g₂o⟩, hr₂, hc₂⟩,
        simp at hr₁ hc₁ hr₂ hc₂, substs hc₁ hr₁ hc₂ hr₂,
        exact vector.zip_with (+) g₁d g₂d
      end⟩, ⟨0, 0⟩⟩, rfl, rfl⟩
}

def transpose (m₁ : matrix m n α) : matrix n m α :=
  ⟨(vec_grid₀_of_fgrid₀ ⟨
      n, m, mul_comm m n ▸ @matrix_unempty _ _ _ m₁,
      ⟨m₁.g.o.y, m₁.g.o.x⟩,
      λx y, abs_data m₁.g ⟨
        ⟨y.1,
        begin
          cases y with y h, simp at h, simp [expand_gtr, grid.bl],
          have : ↑(rows (m₁.g)) = ↑m,
            by rcases m₁ with ⟨⟨⟨_, _, _, _⟩, _⟩, h₁, h₂⟩; substs h₁ h₂; simp [rows],
          rw this, exact h
        end⟩,
        ⟨x.1,
        begin
          cases x with x h, simp at h, simp [expand_gtr, grid.bl],
          have : ↑(cols (m₁.g)) = ↑n,
            by rcases m₁ with ⟨⟨⟨_, _, _, _⟩, _⟩, h₁, h₂⟩; substs h₁ h₂; simp [cols],
          rw this, exact h
        end⟩⟩⟩), by simp, by simp⟩

theorem transpose_transpose_id (m₁ : matrix m n α) :
  transpose (transpose m₁) = m₁ :=
begin
  rcases m₁ with ⟨⟨g, ⟨_, _⟩⟩, h₁, h₂⟩, subst h₁, subst h₂,
  unfold transpose, congr' 1,
  ext _; try { simp }, rw gen_aof_eq_gen,
  apply list.ext_le _ _,
    {
      repeat { rw length_generate_eq_size },
      simp [size, rows, cols]
    },
    {
      intros n h₁ h₂, rw nth_le_generate_f₀,
      simp [abs_data_eq_nth_v₀', tl, bl, vector.nth_eq_nth_le, vector.to_list],
      rw [← option.some_inj, ← list.nth_le_nth, nth_vecgrid_of_fgrid],
      have : |↑n % ↑g.c| + g.c * |↑n / ↑g.c| < list.length g.data.val,
        by rw [mul_comm, mod_add_div_coe]; rw generate_eq_data at h₂; exact h₂,
      simp [length_generate_eq_size, size] at h₂,
      have rpos : g.r > 0, from (gt_and_gt_of_mul_gt g.h).1,
      have cpos : g.c > 0, from (gt_and_gt_of_mul_gt g.h).2,
      have nltcr : n < g.r * g.c, by simp [rows, cols, *] at h₂; assumption,
      have h₃ : ↑(n / g.c) < ↑g.r,
        by rwa [int.coe_nat_lt_coe_nat_iff, nat.div_lt_iff_lt_mul _ _ cpos],
      rw nth_generate_f₀,
      simp [abs_data_eq_nth_v₀', vector.nth_eq_nth_le, list.nth_le_nth this, vector.to_list],
      rw [← with_bot.some_eq_coe], simp [generate_eq_data],
      congr,
        {
          have rnezero : g.r ≠ 0, by intros contra; rw contra at rpos; linarith,
          rw ← int.coe_nat_eq_coe_nat_iff, simp,
          repeat { rw int.nat_abs_of_nonneg; try { apply int.coe_zero_le } },
          rw @int.add_mul_div_right _ _ g.r (by simpa),
          norm_cast, rw nat.div_div_eq_div_mul, rw mul_comm g.c g.r,
          simp[@nat.div_eq_of_lt n (g.r * g.c) nltcr],
          norm_cast,
          have h₄ : (0 : ℤ) ≤ ↑(n / g.c), by simp,
          rw @int.mod_eq_of_lt ↑(n / g.c) ↑g.r h₄ h₃, rw mul_comm,
          apply int.mod_add_div
        },
        {
          rw length_generate_eq_size, simp [size, cols, rows],
          rw [add_comm],
          have h₄ : |↑n / ↑g.c| < g.r, by norm_cast at *; exact h₃,
          have h₅ : |↑n % ↑g.c| < g.c,
            begin
              rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg],
              apply @int.mod_lt_of_pos ↑n ↑g.c (by norm_cast; exact cpos),
              have cnezero : g.c ≠ 0, by intros contra; rw contra at cpos; linarith,
              exact int.mod_nonneg _ (by simp [cnezero])
            end,
          exact linearize_array h₄ h₅
        }
    }   
end

end operations

end matrix