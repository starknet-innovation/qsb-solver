import importlib.util
from pathlib import Path
import struct
import unittest
spec=importlib.util.spec_from_file_location('elf_metadata',Path(__file__).resolve().parents[1]/'worker/promotion/validation/elf_metadata.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

def fixture(pid,flags=0,loaded_strings=False):
    names=b'\0.shstrtab\0.strtab\0';strings=b'\0tmpxft_'+pid+b'_00000000-6_pinning.cudafe1.cpp\0';data=bytearray(312+len(names)+len(strings));data[:6]=b'\x7fELF\x02\x01';struct.pack_into('<Q',data,32,256);struct.pack_into('<HH',data,54,56,1);struct.pack_into('<IIQQQQQQ',data,256,1,5,0,0,0,len(data) if loaded_strings else 64,64,4096);struct.pack_into('<Q',data,40,64);struct.pack_into('<HHH',data,58,64,3,1)
    struct.pack_into('<IIQQQQIIQQ',data,128,1,3,0,0,312,len(names),0,0,1,0)
    struct.pack_into('<IIQQQQIIQQ',data,192,11,3,flags,0,312+len(names),len(strings),0,0,1,0)
    data[312:]=names+strings;return bytes(data)

class ElfMetadataTests(unittest.TestCase):
    def test_only_temporary_filename_is_normalized(self):
        a,b=fixture(b'00000009'),fixture(b'0000000a');m.same_except_nvcc_filename(a,b)
        changed=bytearray(b);changed[20]=1
        with self.assertRaises(ValueError):m.same_except_nvcc_filename(a,changed)
    def test_allocated_table_and_missing_symbol_reject(self):
        for data in [fixture(b'00000009',2),fixture(b'00000009',loaded_strings=True),fixture(b'00000009').replace(b'pinning',b'changed'),b'not ELF']:
            with self.assertRaises(ValueError):m.normalized_file_symbols(data)
