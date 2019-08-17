import cautomaton utils

open utils

namespace la

section la

inductive cellT | B | W | BN | BE | BS | BW | WN | WE | WS | WW

inductive antCardinal | AN | AW | AE | AS | A

open cellT antCardinal

def cellT_str : cellT → string 
	| B := "X"
	| W := " "
	| BN := "^"
	| BE := ">"
  | BS := "v"
  | BW := "<"
  | WN := "^"
  | WE := ">"
  | WS := "v"
  | WW := "<"

instance cellT_to_str : has_to_string cellT := ⟨cellT_str⟩

instance cellT_repr : has_repr cellT := ⟨cellT_str⟩

instance cellT_deceq : decidable_eq cellT :=
	λl r,
		begin
			cases l; cases r; try {exact is_true rfl}; apply is_false; trivial
		end

attribute [reducible]
def ant := cautomaton cellT

def step : cellT → antCardinal → cellT
  | W AS := WS
  | B AS := BS
  | W AE := WE
  | B AE := BE
  | W AW := WW
  | B AW := BW
  | W AN := WN
  | B AN := BN
  | BN _ := W
  | BW _ := W
  | BE _ := W
  | BS _ := W
  | WN _ := B
  | WW _ := B
  | WE _ := B
  | WS _ := B
  | x A  := x

def la_step (cell : cellT) (neigh : list cellT) :=
  let north := list.nth neigh 0 in
  match north with
    | none     := W
    | (some c) := if c = WE ∨ c = BW then step cell AS else
  let west := list.nth neigh 1 in
  match west with
    | none     := W
    | (some c) := if c = WN ∨ c = BS then step cell AE else
  let east  := list.nth neigh 2 in
  match east with
    | none     := W
    | (some c) := if c = WS ∨ c = BN then step cell AW else
  let south := list.nth neigh 3 in  
  match south with
    | none     := W
    | (some c) := if c = WW ∨ c = BE then step cell AN else
  step cell A
  end end end end

def mk_ant (g : agrid₀ cellT) : ant :=
  ⟨g, W, cautomatons.neumann, la_step, cautomatons.ext_one⟩

def ant_g :=
  agrid₀.mk ⟨11, 11, dec_trivial,
	          ⟨[W, W, W, W, W, W, W, W, W, W, W,
              W, W, W, W, W, W, W, W, W, W, W,
              W, W, W, W, W, W, W, W, W, W, W,
              W, W, W, W, W, W, W, W, W, W, W,
              W, W, W, W, W, W, W, W, W, W, W,
              W, W, W, W, W, WW, W, W, W, W, W,
              W, W, W, W, W, W, W, W, W, W, W,
              W, W, W, W, W, W, W, W, W, W, W,
              W, W, W, W, W, W, W, W, W, W, W,
              W, W, W, W, W, W, W, W, W, W, W,
              W, W, W, W, W, W, W, W, W, W, W], rfl⟩⟩
						⟨0, 1⟩ 

def simple : ant := mk_ant ant_g

end la

end la