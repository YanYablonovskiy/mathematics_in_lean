#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5

#check List    -- List.{u} (α : Type u) : Type u

#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
#check Prod Nat Type





def F.{u} (α : Type u) : Type u := Prod α α

#check F
