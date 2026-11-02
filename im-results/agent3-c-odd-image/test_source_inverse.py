"""Single test file: exhaustive forward/inverse small-domain comparison."""
from source_inverse import inverse_section
from CSectionOracle import sec


if __name__ == "__main__":
    limit = 350
    checks = 0
    failures = []
    for a in range(limit + 1):
        for k in range(limit + 1):
            target = sec(a, k)
            if target is None:
                continue
            checks += 1
            if (a, k) not in inverse_section(*target):
                failures.append(("missed", (a, k), target))
    for x in range(190):
        for y in range(190):
            for pre in inverse_section(x, y):
                checks += 1
                if sec(*pre) != (x, y):
                    failures.append(("false positive", pre, (x, y), sec(*pre)))
    print("Direct/inverse source-section checks:", checks)
    print("Failures:", len(failures))
    for item in failures[:20]:
        print("Failure:", item)
    assert not failures
