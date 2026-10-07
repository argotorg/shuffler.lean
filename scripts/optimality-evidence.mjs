#!/usr/bin/env node
/** Make a compact evidence manifest from completed benchmark reports. */
import fs from 'node:fs';

const [checkpoint, output, ...summaries] = process.argv.slice(2);
if (!checkpoint || !output || summaries.length === 0) {
  throw new Error('usage: optimality-evidence.mjs CHECKPOINT OUTPUT SUMMARY...');
}
const entries = summaries.sort().map(summaryPath => {
  const summary = JSON.parse(fs.readFileSync(summaryPath, 'utf8'));
  const configuration = summary.configuration;
  const recordsPath = summaryPath.replace('-summary.json', '.jsonl');
  const records = fs.readFileSync(recordsPath, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse);
  const unique = values => [...new Set(values)].sort((a, b) => typeof a === 'number' ? a - b : String(a).localeCompare(String(b)));
  const algorithms = Object.fromEntries(Object.entries(summary.algorithms).map(([name, stats]) => [name, {
    cases: stats.cases, successes: stats.successes, feasibilityFailures: stats.feasibilityFailures,
    oracleComparisons: stats.oracleComparisons, exact: stats.exact,
    zeroExcessViolations: stats.zeroExcessViolations, maxExcessRatio: stats.maxExcessRatio,
    worstExcessCase: stats.worstExcessCase, certificates: stats.certificates ?? null,
    scope: stats.scope ?? (name === 'old-bbu' ? 'original-generation-and-final-permutation' : 'completed-source-to-target'),
    witnessComparisons: stats.witnessComparisons ?? null, witnessViolations: stats.witnessViolations ?? null,
    maxWitnessExcessRatio: stats.maxWitnessExcessRatio ?? null, worstWitnessCase: stats.worstWitnessCase ?? null,
    worstWitnessComparison: stats.worstWitnessComparison ?? null,
    witnessPositiveExcessComparisons: stats.witnessPositiveExcessComparisons ?? null,
    witnessZeroExcessComparisons: stats.witnessZeroExcessComparisons ?? null,
    witnessZeroExcessViolations: stats.witnessZeroExcessViolations ?? null,
    maxCandidateExcessWithZeroWitness: stats.maxCandidateExcessWithZeroWitness ?? null,
    worstZeroExcessWitnessCase: stats.worstZeroExcessWitnessCase ?? null,
  }]));
  const select = configuration.inputPath ? `--input ${configuration.inputPath}` :
    `--suite ${configuration.suite} --seed ${configuration.seed} --cases ${summary.cases}`;
  return {
    suite: configuration.suite, seed: configuration.seed, cases: summary.cases,
    witnessRatioReporting: summary.witnessRatioReporting ?? { version: 1, maximumClampedAtOne: true },
    selectedAlgorithms: configuration.selectedAlgorithms ?? null,
    stateLimit: configuration.stateLimit, skipOracle: configuration.skipOracle ?? false,
    oracle: summary.oracle, oracleStates: summary.oracleStates,
    sourceHeights: unique(records.map(record => record.problem.source.length)),
    targetHeights: unique(records.map(record => record.problem.target.length)),
    gasModels: unique(records.map(record => record.problem.gasModel)),
    loadAddressWidths: unique(records.flatMap(record => record.problem.loadWidths.map(pair => pair[1]))),
    weights: unique(records.map(record => `${record.problem.weights.gas}:${record.problem.weights.bytes}`)),
    productionRunnerSha256: configuration.runnerSnapshot?.sha256 ?? null,
    productionFingerprintsAtRun: { before: configuration.versionBefore, after: configuration.versionAfter },
    modelDisagreements: summary.modelDisagreements, algorithms, summaryPath, recordsPath,
    referenceCertificates: Object.fromEntries(['exactBaseline', 'exactLineage', 'exactStatic', 'exactNoGrowth', 'twiceLineage', 'twiceStatic'].map(name =>
      [name, records.filter(record => record.production?.result?.reference?.certificates?.[name]).length])),
    inputCases: configuration.inputPath ? records.map(record => record.problem) : undefined,
    reproduce: `node scripts/optimality-bench.mjs ${select} --state-limit ${configuration.stateLimit}` +
      (configuration.skipOracle ? ' --skip-oracle' : '') +
      (configuration.selectedAlgorithms ? ' --algorithms ' + configuration.selectedAlgorithms.join(',') : '') +
      ' --runner .lake/build/bin/optimality_bench',
  };
});
const hashes = [...new Set(entries.map(entry => entry.productionRunnerSha256))];
if (hashes.length !== 1 || hashes[0] === null) throw new Error('reports must share one fixed native runner');
fs.writeFileSync(output, JSON.stringify({
  checkpoint, status: 'intermediate experimental checkpoint', productionRunnerSha256: hashes[0],
  reproductionNote: 'Commands regenerate the cases and run the current build. Match the executable hash to repeat this checkpoint exactly. Source and artifact fingerprints were sampled at run time; the executable hash identifies the fixed planner. Input-suite cases are included inline.',
  limits: 'Finite tests do not prove a general approximation ratio. Only optimal oracle records enter cost ratios. A not-run result is an intentional omission, not an optimum or an infeasibility claim. Missing certificate counters mean that coverage was not measured by that runner. A witness violation proves failure of factor two without an optimum; absence of a witness violation is only finite test evidence.',
  suites: entries,
}, null, 2) + '\n');
process.stdout.write(JSON.stringify({ output, suites: entries.length,
  cases: entries.reduce((sum, entry) => sum + entry.cases, 0), productionRunnerSha256: hashes[0] }) + '\n');
