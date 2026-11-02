module

public import PlanBridge.Assembly
public import PlanBridge.Model

/-! The assembly and Shuffler contracts compose through the shared flat model. -/

namespace PlanBridge

public theorem plan_correct : AssemblyContract InputOk ResultOk :=
  kraken_to_flat flat_to_shuffler

public theorem plan_binary_correct : AssemblyBinaryContract InputOk ResultOk :=
  kraken_to_flat_binary flat_to_shuffler

end PlanBridge
