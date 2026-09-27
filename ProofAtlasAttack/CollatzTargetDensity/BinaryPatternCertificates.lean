import CollatzTargetDensity.BinaryPatternPotential

/-! Generated exact certificates; ordinary kernel reduction checks the data. -/
namespace CollatzTargetDensity.BinaryPatternPotential

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def certificate1 : List Edge := [
  ⟨3, 5, 1, 3⟩,
  ⟨5, 1, 4, 1⟩,
  ⟨9, 7, 2, 1⟩
]

theorem certificate1_checked : check 1 certificate1 = true := by decide

def certificate2 : List Edge := [
  ⟨3, 5, 1, 3⟩,
  ⟨5, 1, 4, 1⟩,
  ⟨9, 7, 2, 2⟩,
  ⟨11, 17, 1, 1⟩
]

theorem certificate2_checked : check 2 certificate2 = true := by decide

def certificate3 : List Edge := [
  ⟨3, 5, 1, 3⟩,
  ⟨9, 7, 2, 2⟩,
  ⟨23, 35, 1, 1⟩,
  ⟨33, 25, 2, 1⟩,
  ⟨93, 35, 3, 1⟩
]

theorem certificate3_checked : check 3 certificate3 = true := by decide

def certificate4 : List Edge := [
  ⟨7, 11, 1, 3⟩,
  ⟨9, 7, 2, 3⟩,
  ⟨11, 17, 1, 2⟩,
  ⟨25, 19, 2, 1⟩,
  ⟨33, 25, 2, 1⟩,
  ⟨43, 65, 1, 1⟩,
  ⟨99, 149, 1, 1⟩,
  ⟨133, 25, 4, 1⟩
]

theorem certificate4_checked : check 4 certificate4 = true := by decide

def certificate5 : List Edge := [
  ⟨7, 11, 1, 13⟩,
  ⟨9, 7, 2, 13⟩,
  ⟨11, 17, 1, 15⟩,
  ⟨15, 23, 1, 2⟩,
  ⟨17, 13, 2, 8⟩,
  ⟨25, 19, 2, 1⟩,
  ⟨27, 41, 1, 8⟩,
  ⟨33, 25, 2, 4⟩,
  ⟨35, 53, 1, 2⟩,
  ⟨49, 37, 2, 1⟩,
  ⟨97, 73, 2, 2⟩,
  ⟨101, 19, 4, 1⟩,
  ⟨129, 97, 2, 3⟩,
  ⟨165, 31, 4, 2⟩,
  ⟨285, 107, 3, 2⟩,
  ⟨351, 527, 1, 2⟩,
  ⟨423, 635, 1, 6⟩,
  ⟨573, 215, 3, 2⟩,
  ⟨701, 263, 3, 4⟩,
  ⟨807, 1211, 1, 2⟩
]

theorem certificate5_checked : check 5 certificate5 = true := by decide

def certificate6 : List Edge := [
  ⟨7, 11, 1, 88⟩,
  ⟨11, 17, 1, 119⟩,
  ⟨19, 29, 1, 33⟩,
  ⟨25, 19, 2, 33⟩,
  ⟨27, 41, 1, 16⟩,
  ⟨29, 11, 3, 31⟩,
  ⟨31, 47, 1, 62⟩,
  ⟨33, 25, 2, 33⟩,
  ⟨37, 7, 4, 88⟩,
  ⟨39, 59, 1, 12⟩,
  ⟨41, 31, 2, 62⟩,
  ⟨43, 65, 1, 79⟩,
  ⟨47, 71, 1, 62⟩,
  ⟨49, 37, 2, 69⟩,
  ⟨57, 43, 2, 18⟩,
  ⟨71, 107, 1, 100⟩,
  ⟨73, 55, 2, 16⟩,
  ⟨89, 67, 2, 2⟩,
  ⟨91, 137, 1, 42⟩,
  ⟨97, 73, 2, 20⟩,
  ⟨103, 155, 1, 58⟩,
  ⟨107, 161, 1, 80⟩,
  ⟨121, 91, 2, 44⟩,
  ⟨129, 97, 2, 20⟩,
  ⟨131, 197, 1, 21⟩,
  ⟨137, 103, 2, 63⟩,
  ⟨155, 233, 1, 91⟩,
  ⟨161, 121, 2, 44⟩,
  ⟨171, 257, 1, 4⟩,
  ⟨201, 151, 2, 3⟩,
  ⟨209, 157, 2, 26⟩,
  ⟨233, 175, 2, 55⟩,
  ⟨353, 265, 2, 20⟩,
  ⟨413, 155, 3, 11⟩,
  ⟨417, 313, 2, 26⟩,
  ⟨465, 349, 2, 14⟩,
  ⟨545, 409, 2, 20⟩,
  ⟨559, 839, 1, 30⟩,
  ⟨569, 427, 2, 10⟩,
  ⟨615, 923, 1, 18⟩,
  ⟨687, 1031, 1, 6⟩,
  ⟨807, 1211, 1, 2⟩,
  ⟨933, 175, 4, 2⟩,
  ⟨943, 1415, 1, 20⟩,
  ⟨953, 715, 2, 14⟩,
  ⟨1047, 1571, 1, 19⟩,
  ⟨1051, 1577, 1, 10⟩,
  ⟨1053, 395, 3, 19⟩,
  ⟨1071, 1607, 1, 1⟩,
  ⟨1127, 1691, 1, 2⟩,
  ⟨1437, 539, 3, 12⟩,
  ⟨1465, 1099, 2, 2⟩,
  ⟨1617, 1213, 2, 10⟩,
  ⟨1725, 647, 3, 10⟩
]

theorem certificate6_checked : check 6 certificate6 = true := by decide

def certificate7 : List Edge := [
  ⟨23, 35, 1, 48⟩,
  ⟨31, 47, 1, 200⟩,
  ⟨35, 53, 1, 48⟩,
  ⟨39, 59, 1, 66⟩,
  ⟨41, 31, 2, 200⟩,
  ⟨43, 65, 1, 140⟩,
  ⟨47, 71, 1, 200⟩,
  ⟨55, 83, 1, 24⟩,
  ⟨57, 43, 2, 58⟩,
  ⟨59, 89, 1, 66⟩,
  ⟨61, 23, 3, 48⟩,
  ⟨67, 101, 1, 93⟩,
  ⟨71, 107, 1, 200⟩,
  ⟨73, 55, 2, 24⟩,
  ⟨81, 61, 2, 54⟩,
  ⟨87, 131, 1, 11⟩,
  ⟨89, 67, 2, 66⟩,
  ⟨91, 137, 1, 194⟩,
  ⟨97, 73, 2, 20⟩,
  ⟨103, 155, 1, 128⟩,
  ⟨107, 161, 1, 248⟩,
  ⟨109, 41, 3, 99⟩,
  ⟨121, 91, 2, 136⟩,
  ⟨123, 185, 1, 6⟩,
  ⟨129, 97, 2, 84⟩,
  ⟨131, 197, 1, 4⟩,
  ⟨137, 103, 2, 134⟩,
  ⟨139, 209, 1, 62⟩,
  ⟨145, 109, 2, 99⟩,
  ⟨155, 233, 1, 134⟩,
  ⟨161, 121, 2, 194⟩,
  ⟨193, 145, 2, 91⟩,
  ⟨199, 299, 1, 12⟩,
  ⟨201, 151, 2, 31⟩,
  ⟨233, 175, 2, 56⟩,
  ⟨235, 353, 1, 8⟩,
  ⟨263, 395, 1, 56⟩,
  ⟨265, 199, 2, 12⟩,
  ⟨303, 455, 1, 49⟩,
  ⟨343, 515, 1, 20⟩,
  ⟨353, 265, 2, 41⟩,
  ⟨393, 295, 2, 60⟩,
  ⟨403, 605, 1, 6⟩,
  ⟨417, 313, 2, 54⟩,
  ⟨437, 41, 5, 23⟩,
  ⟨455, 683, 1, 49⟩,
  ⟨485, 91, 4, 58⟩,
  ⟨513, 385, 2, 56⟩,
  ⟨559, 839, 1, 4⟩,
  ⟨583, 875, 1, 23⟩,
  ⟨609, 457, 2, 31⟩,
  ⟨687, 1031, 1, 15⟩,
  ⟨777, 583, 2, 29⟩,
  ⟨815, 1223, 1, 7⟩,
  ⟨839, 1259, 1, 12⟩,
  ⟨885, 83, 5, 19⟩,
  ⟨933, 175, 4, 31⟩,
  ⟨1071, 1607, 1, 2⟩,
  ⟨1223, 1835, 1, 23⟩,
  ⟨1491, 2237, 1, 2⟩,
  ⟨1653, 155, 5, 6⟩,
  ⟨2361, 1771, 2, 54⟩,
  ⟨2437, 457, 4, 4⟩,
  ⟨2735, 4103, 1, 14⟩,
  ⟨2981, 559, 4, 4⟩,
  ⟨3243, 4865, 1, 35⟩,
  ⟨3261, 1223, 3, 16⟩,
  ⟨3539, 5309, 1, 35⟩,
  ⟨3741, 1403, 3, 6⟩,
  ⟨3769, 2827, 2, 6⟩,
  ⟨3773, 1415, 3, 27⟩
]

theorem certificate7_checked : check 7 certificate7 = true := by decide

/-- This covers widths one through seven, with arbitrary real weights.
It makes no assertion about larger widths or other potential families. -/
theorem no_width_le_seven (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 7) (w : ℕ → ℝ) :
    ¬StrictDescent k w := by
  interval_cases k
  · exact check_not_descent 1 certificate1 certificate1_checked w
  · exact check_not_descent 2 certificate2 certificate2_checked w
  · exact check_not_descent 3 certificate3 certificate3_checked w
  · exact check_not_descent 4 certificate4 certificate4_checked w
  · exact check_not_descent 5 certificate5 certificate5_checked w
  · exact check_not_descent 6 certificate6 certificate6_checked w
  · exact check_not_descent 7 certificate7 certificate7_checked w

end CollatzTargetDensity.BinaryPatternPotential
