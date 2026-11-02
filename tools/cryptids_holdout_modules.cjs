'use strict';

/**
 * Date-pinned, filename-level cross-reference between the historic six-state
 * holdout snapshot and the external Cryptids Lean module inventory.
 *
 * The output records upstream module existence and separately documents the
 * theorem-predicate names advertised by pinned upstream README tables. Neither
 * metadata field certifies an individual theorem, current halt status, or BB bound.
 */
const fs = require('node:fs');
const path = require('node:path');

const root = path.resolve(__dirname, '..');
const holdoutsPath = path.join(root, 'resources', 'BB6_holdouts_663_2026-10-16.txt');
const modulesPath = path.join(root, 'resources', 'cryptids-bb6-modules-c86f1586.txt');
const predicatePath = path.join(root, 'resources', 'cryptids-bb6-predicates-c86f1586.tsv');
const sourceCommit = 'c86f15861709b76042998c5211c7b2f83991621b';

const holdouts = fs.readFileSync(holdoutsPath, 'utf8').trim().split(/\r?\n/);
const holdoutSet = new Set(holdouts);
const modules = fs.readFileSync(modulesPath, 'utf8').split(/\r?\n/)
  .filter((line) => line !== '' && !line.startsWith('#'));
const declaredPredicates = new Map(fs.readFileSync(predicatePath, 'utf8').split(/\r?\n/)
  .filter((line) => line.startsWith('1'))
  .map((line) => {
    const [rootedRle, documentationPath, predicates] = line.split('\t');
    return [rootedRle, { documentation_path: documentationPath,
      upstream_declared_predicates: predicates.split(';') }];
  }));

/** @param {string} sourcePath */
function toRootedRle(sourcePath) {
  const filename = path.posix.basename(sourcePath, '.lean');
  return filename.slice(2).replaceAll('HHH', '---');
}

const entries = modules.map((sourcePath) => ({
  rooted_rle: toRootedRle(sourcePath),
  source_path: sourcePath,
  source_directory: sourcePath.includes('/Accelerations/') ? 'Accelerations' : 'BB6',
  ...declaredPredicates.get(toRootedRle(sourcePath)),
  appears_in_2026_10_16_snapshot: holdoutSet.has(toRootedRle(sourcePath)),
}));

const matching = entries.filter((entry) => entry.appears_in_2026_10_16_snapshot)
  .sort((a, b) => a.rooted_rle.localeCompare(b.rooted_rle));
const outsideSnapshot = entries.filter((entry) => !entry.appears_in_2026_10_16_snapshot)
  .sort((a, b) => a.rooted_rle.localeCompare(b.rooted_rle));

const report = {
  snapshot: '2026-10-16',
  upstream_repository: 'google-deepmind/cryptids',
  upstream_commit: sourceCommit,
  upstream_module_count: modules.length,
  snapshot_rooted_count: holdouts.length,
  roots_with_upstream_module: matching.length,
  roots_without_upstream_module: holdouts.length - new Set(matching.map((e) => e.rooted_rle)).size,
  source_files_outside_snapshot: outsideSnapshot.length,
  predicates_declared_in_docs: Object.fromEntries(
    [...new Set(matching.flatMap((e) => e.upstream_declared_predicates))]
      .sort().map((predicate) => [predicate,
        matching.filter((e) => e.upstream_declared_predicates.includes(predicate)).length])
  ),
  matching,
  outsideSnapshot,
  evidence_limit: 'Source README predicate claims and module filenames only; no independent theorem-level audit or current halting classification inferred.',
};

if (require.main === module) {
  process.stdout.write(JSON.stringify(report, null, 2) + '\n');
}

module.exports = { toRootedRle, report };
