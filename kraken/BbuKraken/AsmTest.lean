import BbuKraken.Asm

namespace Bbu

set_option maxRecDepth 100000

-- The function programs make up the linked file.
example : bbuAsm = isSpilledAsm ++ positionOfAsm ++ shallowestCopyAsm ++ swapWithAsm ++ pushAsm
    ++ dupAsm ++ produceAsm ++ generateAsm ++ finishAsm ++ loopAsm ++ buildBottomUpAsm := by rfl

end Bbu
