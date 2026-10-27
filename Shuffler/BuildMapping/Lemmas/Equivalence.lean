import Shuffler.BuildMapping.Defs

namespace Shuffler.BuildMapping.Equivalence

theorem closestCopy_eq {source target : Stack} (self : MappingBuilder source target)
    (targetOffset : Fin target.length) (location : CopyLocation) :
    self.closestCopy_new targetOffset location = self.closestCopy targetOffset location := by
  simp only [MappingBuilder.closestCopy_new, MappingBuilder.closestCopy, bind_pure]
  congr 1
  funext i best
  congr 1
  funext mappable
  cases location <;> cases mappable <;> cases best <;> simp

end Shuffler.BuildMapping.Equivalence
