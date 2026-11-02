'use strict';

/**
 * Date-pinned, filename-level cross-reference between the historic six-state
 * holdout snapshot and the external Cryptids Lean module inventory.
 *
 * The output says where source files exist. It never infers a halt decision,
 * certified acceleration level, current unresolved status, or BB(6) bound.
 */
const fs = require('node:fs');
const path = require('node:path');

const root = path.resolve(__dirname, '..');
const holdoutsPath = path.join(root, 'resources', 'BB6_holdouts_663_2026-10-16.txt');
const modulesPath = path.join(root, 'resources', 'cryptids-bb6-modules-c86f1586.txt');
const sourceCommit = 'c86f15861709b76042998c5211c7b2f83991621b';

const holdouts = fs.readFileSync(holdoutsPath, 'utf8').trim().split(/\r?\n/);
const holdoutSet = new Set(holdouts);
const modules = fs.readFileSync(modulesPath, 'utf8').split(/\r?\n/)
  .filter((line) => line !== '' && !line.startsWith('#'));

/** @param {string} sourcePath */
function toRootedRle(sourcePath) {
  const filename = path.posix.basename(sourcePath, '.lean');
  return filename.slice(2).replaceAll('HHH', '---');
}

const entries = modules.map((sourcePath) => ({
  rooted_rle: toRootedRle(sourcePath),
  source_path: sourcePath,
  source_directory: sourcePath.includes('/Accelerations/') ? 'Accelerations' : 'BB6',
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
  matching,
  outsideSnapshot,
  evidence_limit: 'Filename-level RLE correspondence only; no individual theorem or current halting classification inferred.',
};

if (require.main === module) {
  process.stdout.write(JSON.stringify(report, null, 2) + '\n');
}

module.exports = { toRootedRle, report };
