import «Chapter2» 
import «Main»


lemma DualOfVpolytope_compactHpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite)
  (horigin : 0 ∈ interior (Vpolytope hS)) : 