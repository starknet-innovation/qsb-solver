"""One-shot disposable LOCAL REGTEST wallet. Never upload the private directory.

No funding, networking, signing or solver execution. Mainnet-formatted addresses
exist only because the offline-fixture schema uses them; never fund this address.
"""
import argparse
import contextlib
from datetime import datetime, timezone
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import secrets
import sys
import tempfile
import uuid

SOURCE_HASHES = {
    'bitcoin_tx.py':'c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c',
    'secp256k1.py':'d2cebd1410b75cad606806cf02d7bee3e24724d5fcb7a53a07f598fcbc8afece',
    'qsb_pipeline.py':'05334c08fa012a77ccba2887e05d78f90a8b81c0e34b786931b423f7f11255d8',
    'bridge.py':'ba02b56d763533ca144f9ea17cfab6f01dd87d9658a17c4af8744c75803455e2',
}


def nested_address(public):
    h160=lambda b:hashlib.new('ripemd160',hashlib.sha256(b).digest()).digest()
    payload=b'\x05'+h160(b'\x00\x14'+h160(public))
    checksum=hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
    number=int.from_bytes(payload+checksum,'big');result=''
    alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
    while number:
        number,rem=divmod(number,58);result=alphabet[rem]+result
    return result


def save_private(path, value):
    fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
    with os.fdopen(fd,'w') as stream:
        json.dump(value,stream,sort_keys=True);stream.write('\n')
        stream.flush();os.fsync(stream.fileno())


def verify_sources(source):
    for name,digest in SOURCE_HASHES.items():
        file=source/name
        if file.is_symlink() or hashlib.sha256(file.read_bytes()).hexdigest()!=digest:
            raise ValueError('Public reference source mismatch: '+name)


def prepare(source, destination):
    source=Path(source).resolve();destination=Path(destination).absolute()
    verify_sources(source)
    # A failed preparation must be inspected; never overwrite it or reuse its identity.
    destination.mkdir(mode=0o700)
    private=destination/'private';private.mkdir(mode=0o700)
    public_dir=destination/'public';public_dir.mkdir(mode=0o700)
    old_umask=os.umask(0o077)
    old_cwd=Path.cwd()
    try:
        with tempfile.TemporaryDirectory(prefix='setup-',dir=private) as staging:
            staging=Path(staging)
            for name in SOURCE_HASHES:
                (staging/name).write_bytes((source/name).read_bytes())
            verify_sources(staging)
            # New interpreter only: reference imports and cwd are process-global.
            if any(name in sys.modules for name in ('bridge','qsb_pipeline','bitcoin_tx','secp256k1')):
                raise ValueError('Use a fresh Python process')
            sys.path.insert(0,str(staging));os.chdir(staging)
            import bridge
            import secp256k1 as secp
            with contextlib.redirect_stdout(io.StringIO()):
                generated=json.loads(bridge.generate())
            scalar=secrets.randbelow(secp.N-1)+1
            public=secp.compress_pubkey(secp.point_mul(scalar,secp.G))
            identity=str(uuid.uuid4())
            wallet=dict(address=nested_address(public),publicKey=public.hex(),type='p2sh')
            save_private(private/'wallet.json',dict(privateKeyHex=f'{scalar:064x}',**wallet))
            save_private(private/'recovery.json',json.loads(generated['stateJson']))
            vault=dict(id=identity,name='Offline signing test — never fund',
                createdAt=datetime.now(timezone.utc).isoformat().replace('+00:00','Z'),
                network='mainnet',config='A',scriptHex=generated['scriptHex'],
                scriptHash=generated['scriptHash'],paymentAddress=wallet['address'],
                publicStateJson=generated['publicStateJson'],status='unfunded')
            request=dict(format='qsb-offline-fixture-request-v1',id=identity,
                         fixtureChain='regtest',wallet=wallet,vault=vault)
            save_private(public_dir/'public-request.json',request)
            request_hash=hashlib.sha256((public_dir/'public-request.json').read_bytes()).hexdigest()
            receipt=dict(requestId=identity,requestSha256=request_hash,sourceHashes=SOURCE_HASHES,
                         network='regtest',wallet='new disposable local wallet',
                         funded=False,mainnetAuthorized=False,privateMaterialUploaded=False)
            save_private(public_dir/'preparation.json',receipt)
        for directory in (private,public_dir,destination,destination.parent):
            fd=os.open(directory,os.O_RDONLY)
            try:os.fsync(fd)
            finally:os.close(fd)
        return receipt
    finally:
        os.chdir(old_cwd);os.umask(old_umask)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--destination',type=Path,required=True)
    args=parser.parse_args()
    try:
        print(json.dumps(prepare(args.source,args.destination),sort_keys=True))
    except Exception as error:
        # Do not print reference exceptions or locals that might contain private state.
        print('Local preparation failed: '+type(error).__name__,file=sys.stderr)
        sys.exit(2)
