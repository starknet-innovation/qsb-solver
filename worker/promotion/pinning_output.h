#pragma once
#include <stdint.h>
#include <stdio.h>

// Return failure before completion can be published. Partial files are never
// evidence of a complete range; the process caller exits nonzero on failure.
static bool qsb_publish_pinning_hits(const char *path, uint32_t sequence,
                                    uint32_t base_locktime, const uint32_t *hits,
                                    uint32_t count) {
    if (count > 64) return false;
    FILE *file = fopen(path, "a");
    if (!file) return false;
    for (uint32_t i = 0; i < count; ++i) {
        uint32_t raw = hits[i];
        fprintf(file, "sequence=%u\nlocktime=%u\nhash_choice=%d\nrecid=%d\n",
                sequence, base_locktime + (raw & 0x3fffffff),
                (int)((raw >> 31) & 1), (int)((raw >> 30) & 1));
    }
    bool failed = ferror(file) != 0;
    if (fclose(file) != 0) failed = true;
    return !failed;
}
