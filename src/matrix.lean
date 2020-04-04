-- Formalization of matrices defined over 'grid's.

import grid utils data.vector2 tactic.elide

open utils

namespace matrix

structure matrix (m n : ℕ) (α : Type) :=
  (g  : dep_vec_grid₀ α m n)

def matrix_of_f {m n} {α} (h : m * n > 0) (f : fin m → fin n → α) : matrix m n α :=
  ⟨⟨h, ⟨℘(fgrid₀.mk m n h ⟨0, 0⟩
    (λx y, f 
      ⟨|x.1|,
       begin
         rcases x with ⟨x, ⟨hx₁, hx₂⟩⟩, simp at hx₁ hx₂ ⊢, 
         rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg hx₁],
         exact hx₂
       end⟩
      ⟨|y.1|,
       begin
         rcases y with ⟨y, ⟨hy₁, hy₂⟩⟩, simp at hy₁ hy₂ ⊢, 
         rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg hy₁],
         exact hy₂
       end
      ⟩)), by simpa [length_generate_eq_size, size]⟩, ⟨0, 0⟩⟩⟩

def matrix_at {m n} {α} (m₁ : matrix m n α) (i : fin m) (j : fin n) : α :=
  abs_data m₁.1 ⟨⟨i.1,
    begin
      rcases m₁ with ⟨⟨h, v, p⟩⟩, simp [grid.bl, expand_gtr, relative_grid.rows],
      
    end⟩, ⟨j.1, sorry⟩⟩

section ext

variables {m n : ℕ} {α : Type} {m₁ m₂ : matrix m n α}

theorem ext_iff : m₁.g = m₂.g ↔ m₁ = m₂ :=
  by cases m₁; rcases m₂; simp

@[extensionality] theorem ext : m₁.g = m₂.g → m₁ = m₂ := ext_iff.1

end ext

section operations

variables {m n o p : ℕ} {α β γ δ : Type}

open relative_grid grid

lemma matrix_nonempty {m₁ : matrix m n α} : m * n > 0 := m₁.1.1

def matrix_string [has_to_string α] (m : matrix m n α) :=
  grid_str m.g

instance matrix_repr [has_to_string α] : has_repr (matrix m n α) :=
  ⟨matrix_string⟩

instance matrix_to_string [has_to_string α] : has_to_string (matrix m n α) :=
  ⟨matrix_string⟩

instance matrix_functor : functor (matrix m n) := {
  map := λα β f m, ⟨f <$> m.g⟩
}

instance matrix_functor_law : is_lawful_functor (matrix m n) := {
  id_map := λα ⟨⟨r, c, h⟩⟩, by simp [(<$>), vector.map_id],
  comp_map := λα β γ f h ⟨⟨r, c, h⟩⟩, by simp [(<$>)]
}

def m₁ : matrix 5 2 ℕ :=
  matrix.mk
    (@dep_vec_grid₀.mk _ 5 2 dec_trivial
                       ⟨[1, 3, 4, 5, 7, 8, 9, 10, 11, 12], dec_trivial⟩ ⟨5, 1⟩)

def m₂ : matrix 2 3 ℕ :=
  matrix.mk
    (@dep_vec_grid₀.mk _ 2 3 dec_trivial
                       ⟨[2, 2, 2, 2, 2, 2], dec_trivial⟩ ⟨0, 0⟩)

instance [has_add α] : has_add (matrix m n α) := {
  add := λm₁ m₂, ⟨
    @dep_vec_grid₀.mk _ m n m₁.1.1 (vector.zip_with (+) m₁.1.2 m₂.1.2) ⟨0, 0⟩
  ⟩
}

def transpose (m₁ : matrix m n α) : matrix n m α :=
  ⟨dep_vec_grid₀_of_fgrid₀
    ⟨
      n, m, mul_comm m n ▸ @matrix_nonempty _ _ _ m₁,
      ⟨m₁.g.o.y, m₁.g.o.x⟩,
      λx y, abs_data m₁.g ⟨y, x⟩
    ⟩
  ⟩

theorem transpose_transpose_id (m₁ : matrix m n α) :
  transpose (transpose m₁) = m₁ :=
begin
  rcases m₁ with ⟨h, data, p⟩,
  unfold transpose, congr' 1,  unfold dep_vec_grid₀_of_fgrid₀, simp, split,
    {
      cases data with data hdata, congr,
      apply list.ext_le _ _,
        {
          repeat { rw length_generate_eq_size },
          simp [size, rows, cols, hdata]
        },
        {
          intros i h₁ h₂, rw nth_le_generate_f₀,
          simp [
            abs_data_eq_nth_v₀', tl, bl, vector.nth_eq_nth_le, vector.to_list
          ],
          have : |↑i % ↑n| + n * |↑i / ↑n| < list.length data,
            by rw [mul_comm, mod_add_div_coe]; exact h₂,
          simp [length_generate_eq_size, size] at h₂,
          have rpos : m > 0, from (gt_and_gt_of_mul_gt h).1,
          have cpos : n > 0, from (gt_and_gt_of_mul_gt h).2,
          have nltcr : i < m * n, by simp [rows, cols, *] at h₂; assumption,
          have h₃ : ↑(i / n) < ↑m,
            by rwa [int.coe_nat_lt_coe_nat_iff, nat.div_lt_iff_lt_mul _ _ cpos],
          simp [dep_vec_grid₀_of_fgrid₀, abs_data, contents, vector.nth],
          repeat { rw [← option.some_inj, ← list.nth_le_nth] },
          simp [relpoint_of_gpoint, bl],
          rw nth_generate_f₀,
          simp [
            abs_data_eq_nth_v₀', vector.nth_eq_nth_le, list.nth_le_nth this,
            vector.to_list
          ],
          rw [← with_bot.some_eq_coe, ← list.nth_le_nth], 
          congr,
            {
              have rnezero : m ≠ 0, by intros contra; rw contra at rpos; linarith,
              rw ← int.coe_nat_eq_coe_nat_iff, simp,
              repeat { rw int.nat_abs_of_nonneg; try { apply int.coe_zero_le } },
              rw @int.add_mul_div_right _ _ m (by simpa),
              norm_cast, rw nat.div_div_eq_div_mul, rw mul_comm n m,
              simp[@nat.div_eq_of_lt i (m * n) nltcr],
              norm_cast,
              have h₄ : (0 : ℤ) ≤ ↑(i / n), by simp,
              rw @int.mod_eq_of_lt ↑(i / n) ↑m h₄ h₃, rw mul_comm,
              apply int.mod_add_div
            },
            {
              rw length_generate_eq_size, simp [size, cols, rows],
              rw [add_comm],
              have h₄ : |↑i / ↑n| < m, by norm_cast at *; exact h₃,
              have h₅ : |↑i % ↑n| < n,
                begin
                  rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg],
                  apply @int.mod_lt_of_pos ↑i ↑n (by norm_cast; exact cpos),
                  have cnezero : n ≠ 0, by intros contra; rw contra at cpos; linarith,
                  exact int.mod_nonneg _ (by simp [cnezero])
                end,
              exact linearize_array h₄ h₅
            }
        }
    },
    {
      cases p, refl
    }  
end

end operations

end matrix