"""Narrow audit comparison; never rewrites binaries or their release identities."""
import re
import struct


def normalized_file_symbols(data):
    if data[:6] != b'\x7fELF\x02\x01' or len(data)<64:
        raise ValueError('expected ELF64 little endian')
    phoff=struct.unpack_from('<Q',data,32)[0]
    phsize,phcount=struct.unpack_from('<HH',data,54)
    if phsize!=56 or phcount==0 or phoff+phsize*phcount>len(data):
        raise ValueError('invalid program header inventory')
    loaded=[]
    for i in range(phcount):
        h=struct.unpack_from('<IIQQQQQQ',data,phoff+i*phsize)
        if h[0]==1:
            if h[2]+h[5]>len(data): raise ValueError('invalid load segment bounds')
            loaded.append((h[2],h[2]+h[5]))
    if not loaded: raise ValueError('missing load segments')
    offset=struct.unpack_from('<Q',data,40)[0]
    size,count,names_index=struct.unpack_from('<HHH',data,58)
    if size!=64 or not 0<names_index<count or offset+size*count>len(data):
        raise ValueError('invalid section inventory')
    sections=[struct.unpack_from('<IIQQQQIIQQ',data,offset+i*size) for i in range(count)]
    def section_bytes(s):
        start,length=s[4:6]
        if start+length>len(data): raise ValueError('invalid section bounds')
        return data[start:start+length]
    names=section_bytes(sections[names_index]);out=bytearray(data);found=0
    for s in sections:
        if s[0]>=len(names): raise ValueError('invalid section name')
        if names[s[0]:].split(b'\0',1)[0]!=b'.strtab':continue
        if s[1]!=3 or s[2]!=0: raise ValueError('not a nonallocated string table')
        found+=1;strings=section_bytes(s)
        pattern=rb'(?<=\x00)tmpxft_([0-9a-f]{8})_00000000-6_pinning\.cudafe1\.cpp(?=\x00)'
        matches=list(re.finditer(pattern,strings))
        if len(matches)!=1:raise ValueError('unexpected nvcc filename inventory')
        m=matches[0];start=s[4]+m.start(1)
        if any(start<end and start+8>begin for begin,end in loaded):
            raise ValueError('nvcc filename overlaps a load segment')
        out[start:start+8]=b'00000000'
    if found!=1:raise ValueError('missing/duplicate string table')
    return bytes(out)


def same_except_nvcc_filename(left,right):
    if normalized_file_symbols(left)!=normalized_file_symbols(right):
        raise ValueError('rebuilt pinning differs beyond nonloaded nvcc filename')
