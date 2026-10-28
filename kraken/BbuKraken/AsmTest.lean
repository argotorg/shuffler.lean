import BbuKraken.Asm

namespace Bbu

set_option maxRecDepth 100000

-- The function programs make up the linked file.
example : bbuAsm = isSpilledAsm ++ positionOfAsm ++ shallowestCopyAsm ++ addAsm ++ swapWithAsm
    ++ produceAsm ++ generateAsm ++ finishAsm ++ takeBoundAsm ++ urgentAsm ++ stepAsm
    ++ buildBottomUpAsm := by rfl

end Bbu
