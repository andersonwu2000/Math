import MATH.Category.Basic.Shapes

open category
namespace order

abbrev PreOrder (C : Category) := Thin C

class PartialOrder (C : Category) extends PreOrder C, Skeletal C

class LinearOrder (C : Category) extends PartialOrder C, Connected C
