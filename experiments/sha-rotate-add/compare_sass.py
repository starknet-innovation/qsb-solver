"""Summarise and compare `cuobjdump -sass` listings. Static code-shape data only: not timing, not correctness."""
import collections, hashlib, json, pathlib, re, sys

FUNCTION = re.compile(r'^\s*Function\s*:\s*(\S+)')
INSTRUCTION = re.compile(r'/\*[0-9a-fA-F]{4,}\*/\s+(?:@!?P\d+\s+)?([A-Z][A-Z0-9_]*(?:\.[A-Z0-9_]+)*)')


def summarise(text):
    """Per-function instruction count and opcode histogram, plus totals."""
    functions = {}; current = None
    for line in text.splitlines():
        match = FUNCTION.match(line)
        if match:
            current = functions.setdefault(match.group(1), collections.Counter()); continue
        match = INSTRUCTION.search(line)
        if match and current is not None:
            current[match.group(1)] += 1
    if not functions or not any(functions.values()):
        raise ValueError('No SASS instructions found')
    total = collections.Counter()
    for histogram in functions.values(): total.update(histogram)
    return {
        'sassSha256': hashlib.sha256(text.encode()).hexdigest(),
        'instructions': sum(total.values()),
        'opcodes': dict(sorted(total.items())),
        'functions': {name: {'instructions': sum(h.values()), 'opcodes': dict(sorted(h.items()))}
                      for name, h in sorted(functions.items())},
    }


def base_opcode_counts(opcodes, base):
    return sum(count for name, count in opcodes.items() if name.split('.')[0] == base)


def compare(baseline, candidate):
    """Signed differences, candidate minus baseline. Zero entries are omitted."""
    def delta(a, b):
        return {k: b.get(k, 0) - a.get(k, 0) for k in sorted(set(a) | set(b)) if b.get(k, 0) != a.get(k, 0)}
    functions = {}
    for name in sorted(set(baseline['functions']) | set(candidate['functions'])):
        a = baseline['functions'].get(name, {'instructions': 0, 'opcodes': {}})
        b = candidate['functions'].get(name, {'instructions': 0, 'opcodes': {}})
        if a != b:
            functions[name] = {'instructions': b['instructions'] - a['instructions'],
                               'opcodes': delta(a['opcodes'], b['opcodes'])}
    return {
        'identicalSass': baseline['sassSha256'] == candidate['sassSha256'],
        'instructions': candidate['instructions'] - baseline['instructions'],
        'leaInstructions': base_opcode_counts(candidate['opcodes'], 'LEA') - base_opcode_counts(baseline['opcodes'], 'LEA'),
        'opcodes': delta(baseline['opcodes'], candidate['opcodes']),
        'functions': functions,
    }


def main(argv):
    if len(argv) < 3:
        raise SystemExit('usage: compare_sass.py BASELINE.sass NAME=VARIANT.sass [...]')
    baseline = summarise(pathlib.Path(argv[1]).read_text())
    report = {'scope': 'Static instruction counts. Not a timing or correctness result.',
              'baseline': baseline, 'variants': {}}
    for item in argv[2:]:
        name, _, path = item.partition('=')
        if not name or not path: raise SystemExit('Variant must be NAME=PATH')
        summary = summarise(pathlib.Path(path).read_text())
        report['variants'][name] = {'summary': summary, 'delta': compare(baseline, summary)}
    json.dump(report, sys.stdout, indent=2, sort_keys=True); sys.stdout.write('\n')


if __name__ == '__main__':
    main(sys.argv)
