"""Serialize complete artifact rows as arguments to the proved finite constructor."""
import investigate


def word(values):
    assert isinstance(values, list) and all(type(n) is int and n >= 0 for n in values)
    return investigate.ml_list(values, investigate.ml_nat)


def artifact(source):
    assert set(source) == {'carrier', 'incidence', 'counted_data', 'functional_data'}

    def pair(row):
        assert isinstance(row, list) and len(row) == 2
        return '(' + word(row[0]) + ',' + word(row[1]) + ')'

    def edge(row):
        assert isinstance(row, list) and len(row) == 3
        return '(' + word(row[0]) + ',' + pair(row[1:]) + ')'

    return '(N.finite_enumerated_artifact ' + ' '.join([
        investigate.ml_list(source['carrier'], word),
        investigate.ml_list(source['incidence'], edge),
        investigate.ml_list(source['counted_data'], pair),
        investigate.ml_list(source['functional_data'], pair)]) + ')'
