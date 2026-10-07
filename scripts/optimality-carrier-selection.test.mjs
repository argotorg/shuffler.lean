import assert from 'node:assert/strict';
import test from 'node:test';
import { structuralCarrierPaths } from './optimality-carrier-selection.mjs';
import { carrierRealization } from './optimality-one-gap.mjs';

test('structural rule picks a direct path when the last early root is late enough', () => {
  const word = ['a', 'b', 'b', 'c', 'c', 'd', 'a'];
  assert.deepEqual(structuralCarrierPaths(word, 3), [[3, 6]]);
  assert.ok(carrierRealization(word, 3, [3, 6]));
});

test('structural rule lists every qualifying intermediate position', () => {
  const word = ['a', 'b', 'b', 'c', 'c', 'd', 'd', 'e', 'a'];
  const paths = structuralCarrierPaths(word, 4);
  assert.deepEqual(paths, [[3, 5, 8], [3, 6, 8], [3, 7, 8]]);
  for (const path of paths) assert.ok(carrierRealization(word, 4, path));
});

test('a supplied carrier path must obey the reach bounds', () => {
  assert.throws(() => carrierRealization(['a', 'b', 'b', 'c', 'a'], 2, [1, 4]), /carrier path/);
});
