// Local public-only export for a second implementation's verification.
import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { selectedRecords } from './reference-records';
const [checkpoint, output] = process.argv.slice(2);
if (!checkpoint || !output || existsSync(output)) throw Error('New output path required');
const state = JSON.parse(readFileSync(checkpoint, 'utf8'));
const input = JSON.parse(readFileSync(join(dirname(checkpoint), 'input.json'), 'utf8'));
const records = selectedRecords(state, input);
if (!records.length) throw Error('No currently selected solution to export');
writeFileSync(output, JSON.stringify({ format: 'qsb-public-upstream-crosscheck-v1', records }, null, 2) + '\n', { flag: 'wx' });
