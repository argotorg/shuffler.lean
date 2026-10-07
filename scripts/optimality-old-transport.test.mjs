import assert from 'node:assert/strict';
import test from 'node:test';
import { oldTransportFloor, minimumOldAssignment } from './optimality-old-transport.mjs';

test('separate old-copy lifts exceed the pooled distance in the saved case', () => {
  assert.equal(oldTransportFloor(16, 2, 20), 4);
  assert.equal(minimumOldAssignment(16, 2, 20).cost, 4);
  assert.equal(Math.ceil(2 * 20 / 16), 3);
});

test('assignment can keep already-correct equal old positions fixed', () => {
  assert.equal(minimumOldAssignment(3, 3, 1).cost, 1);
  assert.equal(minimumOldAssignment(3, 3, 2).cost, 2);
  assert.equal(minimumOldAssignment(3, 3, 3).cost, 3);
  assert.equal(minimumOldAssignment(3, 3, 0).cost, 0);
  assert.equal(minimumOldAssignment(3, 0, 5).cost, 0);
});

test('the closed form agrees with every small exact assignment', () => {
  for (let reach = 1; reach <= 6; reach++) for (let old = 0; old <= reach; old++) {
    for (let fresh = 0; fresh <= 3 * reach; fresh++) {
      assert.equal(oldTransportFloor(reach, old, fresh), minimumOldAssignment(reach, old, fresh).cost);
    }
  }
});

test('invalid dimensions do not enter the formula', () => {
  assert.throws(() => oldTransportFloor(0, 0, 0));
  assert.throws(() => oldTransportFloor(2, 3, 0));
  assert.throws(() => minimumOldAssignment(2, 1, -1));
});
