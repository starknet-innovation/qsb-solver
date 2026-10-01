"""Experimental scheduling for independent, side-effect-free verification only.

Consumes verdicts in input order: 0 accepts, 3 is DER-only, others reject.
Exceptions before acceptance propagate; later speculative exceptions do not.
Not wired into a production handler or the all-cases diagnostic trace verifier.
Evaluators must be bounded by the caller's outer process deadline. Shutdown waits
for already-running checks, so early acceptance does not guarantee low latency.
"""
from collections import deque
from concurrent.futures import ProcessPoolExecutor
import multiprocessing


def first_verified(evaluate, jobs, workers=1, initializer=None, initargs=()):
    """Return accepted input index or an all-DER-only rejection.

Jobs must be an already-materialized sequence of public verification inputs.
At most ``workers`` checks are outstanding; no worker may mutate shared state.
This preserves serial verdict selection, not serial side effects or work count.
"""
    if not 1 <= workers <= 4:
        raise ValueError('workers must be between 1 and 4')
    count = len(jobs)
    der_only = 0
    if workers == 1:
        if initializer is not None:
            initializer(*initargs)
        for index in range(count):
            verdict = evaluate(jobs[index])
            if verdict == 0:
                return dict(acceptedIndex=index, derOnly=False)
            der_only += verdict == 3
        return dict(acceptedIndex=None, derOnly=bool(count) and der_only == count)
    if not count:
        return dict(acceptedIndex=None, derOnly=False)
    pool = ProcessPoolExecutor(max_workers=workers,
                               mp_context=multiprocessing.get_context('spawn'),
                               initializer=initializer, initargs=initargs)
    pending = deque()
    next_index = 0
    try:
        while next_index < min(workers, count):
            pending.append((next_index, pool.submit(evaluate, jobs[next_index])))
            next_index += 1
        while pending:
            index, future = pending.popleft()
            verdict = future.result()
            if verdict == 0:
                return dict(acceptedIndex=index, derOnly=False)
            der_only += verdict == 3
            if next_index < count:
                pending.append((next_index, pool.submit(evaluate, jobs[next_index])))
                next_index += 1
        return dict(acceptedIndex=None, derOnly=der_only == count)
    finally:
        for _, future in pending:
            future.cancel()
        pool.shutdown(wait=True, cancel_futures=True)
