prelude

structure Point (α : Sort 1) where
  x : α
  y : α

structure Extended (α : Sort 1) extends Point α where
  z : α

inductive Tree (α : Sort 1) where
  | leaf : Tree α
  | node (l : Tree α) (v : α) (r : Tree α) : Tree α

class Marker (α : Sort 1) where
  mark : α → α

instance : Marker Unit' where
  mark u := u
