# External flat shuffler model (copy)

Source repository: https://github.com/argotorg/shuffler.lean
Branch: kraken-bbu
Commit: adb2285

Each file: copy path (under this directory), source path in the repository, SHA-256 of the source file.

- `Permutation/Model.lean`: `kraken/FlatShuffler/Permutation/Model.lean`, 68e03df1e43f1f3b44590827400f3e921e98e226283241b6cdba103b17899475
- `Model.lean`: `kraken/FlatShuffler/Model.lean`, 9a3927aac9e5c27a83f0efb561993e3f7898ea3932c4bc4d6abc130155d09007
- `MapModel.lean`: `kraken/FlatShuffler/MapModel.lean`, 6b21653242354d42b208cc172ae20fd42ee6076f8eef82cd8f50cfba375cbe6b
- `FlatModel.lean`: `kraken/FlatShuffler/FlatModel.lean`, a26a178ac4b584db4fff6733eba41c9c0f030d15602d28f087f252403e71915c
- `FlatPop.lean`: `kraken/FlatShuffler/FlatPop.lean`, 468f8577a7cd37035fe2af1f89f8970ea0d81e4959231de5df6eb2313cb65930
- `FlatSurplus.lean`: `kraken/FlatShuffler/FlatSurplus.lean`, 3bfb448faa7c3bd2776e534a07a6d86b1d7f3c269048d73499185a6197e0bbcd
- `FlatLowest.lean`: `kraken/FlatShuffler/FlatLowest.lean`, d7ac810beb102cbc03ad7b3d183edd7cdf9fafb9024602826afcf4c646bcae69
- `FlatSpill.lean`: `kraken/FlatShuffler/FlatSpill.lean`, c6a12d654a1a22c20ed6e481864b864d3776ae7c231cd1fe4ddeb6c5138d7b9e
- `FlatPlan.lean`: `kraken/FlatShuffler/FlatPlan.lean`, 0a873edc7ce5dd5a7974756d2f8b447cc0567f6e15002045e48ca5674964c582

Rule: only import lines are changed (`FlatShuffler.X` becomes `Lift.Shuffler.Ext.X`).
Do not edit these files. Changes go in other modules.

The repository has no licence file. This copy is local; the owner decides the licence before any publication.
