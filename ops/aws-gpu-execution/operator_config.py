"""Explicit non-secret operator configuration, kept outside Git checkouts."""
import json
import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]

def load_config():
    name = os.environ.get('QSB_AWS_OPERATOR_CONFIG')
    if not name:
        raise ValueError('Set QSB_AWS_OPERATOR_CONFIG to an external operator JSON file')
    path = Path(name).resolve(strict=True)
    if ROOT in path.parents or any((p / '.git').exists() for p in path.parents):
        raise ValueError('Operator configuration must be outside Git checkouts')
    def unique(pairs):
        value = {}
        for k, v in pairs:
            if k in value: raise ValueError('Duplicate operator configuration key')
            value[k] = v
        return value
    value = json.loads(path.read_text(), object_pairs_hook=unique)
    patterns = dict(account=r'[0-9]{12}', profile=r'[A-Za-z0-9_.-]+',
                    region=r'eu-west-1', ami=r'ami-[a-f0-9]{8,17}',
                    subnet=r'subnet-[a-f0-9]{8,17}', vpc=r'vpc-[a-f0-9]{8,17}')
    if not isinstance(value, dict) or set(value) != set(patterns):
        raise ValueError('Unexpected operator configuration fields')
    for key, pattern in patterns.items():
        if not isinstance(value[key], str) or not re.fullmatch(pattern, value[key]):
            raise ValueError('Invalid operator configuration field: ' + key)
    return value

def expected_account():
    return load_config()['account']
