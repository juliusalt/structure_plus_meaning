"""Transport complete native artifacts through the proved exact reference operation."""
import re
import json

import native_program_json
import program_evaluation_json

BEGIN = 'NATIVE_ARTIFACT_STREAM'
ENTRY = 'NATIVE_ARTIFACT_VALUE'
END = 'NATIVE_ARTIFACT_END'
REFERENCE = '__native_complete_artifact__'
TERM_ENTRY = 'NATIVE_TERM_VALUE'
TERM_REFERENCE = '__native_complete_term__'
ARTIFACT_TABLE = 'NATIVE_ARTIFACT_TABLE'
TERM_TABLE = 'NATIVE_TERM_TABLE'
FIELDS = {'carrier', 'incidence', 'counted_data', 'functional_data'}


def word(xs):
    return isinstance(xs, list) and all(type(n) is int and n >= 0 for n in xs)


def program(code, *, parallel=False, terms=False):
    """Replace one shared renderer, leaving every native operation and report intact."""
    original = native_program_json.ARTIFACT_ROWS
    # Streaming reporters already own their record/dictionary boundary. Emitting
    # an incremental dictionary entry inside wemit would split a JSON record.
    if 'fun wemit ' in code:
        import native_footer_stream
        return native_footer_stream.program(code, parallel=parallel, terms=terms)
    if original not in code:
        return code
    assert code.count(original) == 1
    start = original.index('fun jartifact ')
    end = original.index('fun jartifactRow ', start)
    raw = original[start:end].replace('fun jartifact ', 'fun jartifact_raw ', 1)
    renderer = original[:start] + raw + r'''
val native_artifact_rows = ref (N.complete_object_table_rows N.complete_empty_artifacts);
val native_artifact_count = ref 0;
val () = print "NATIVE_ARTIFACT_STREAM {\"version\":1}\n";
fun jartifact rows = let
  val (index,next) = N.complete_artifact_reference rows (!native_artifact_rows);
  val size = length next;
  val () = native_artifact_rows := next;
  val () = if size > !native_artifact_count then
      (native_artifact_count := size;
       print ("NATIVE_ARTIFACT_VALUE " ^ jnat index ^ " " ^ jartifact_raw rows ^ "\n"))
    else ();
  in "{\"__native_complete_artifact__\":" ^ jnat index ^ "}" end;
val () = OS.Process.atExit (fn () =>
  (print ("NATIVE_ARTIFACT_END {\"entries\":" ^ Int.toString (!native_artifact_count) ^ "}\n");
   TextIO.flushOut TextIO.stdOut));
''' + original[end:]
    use_terms = terms and program_evaluation_json.TERM in code
    if use_terms:
        renderer = renderer.replace('val () = print "NATIVE_ARTIFACT_STREAM {\\"version\\":1}\\n";',
            'val native_term_rows = ref N.complete_empty_terms;\nval native_term_count = ref 0;\n'
            'val () = print "NATIVE_ARTIFACT_STREAM {\\"version\\":2}\\n";')
        renderer = renderer.replace('^ Int.toString (!native_artifact_count) ^ "}\\n"',
            '^ Int.toString (!native_artifact_count) ^ ",\\"terms\\":" ^ Int.toString (!native_term_count) ^ "}\\n"')
    if parallel:
        renderer = renderer.replace('= ref ', '= Unsynchronized.ref ')
    code = code.replace(original, renderer, 1)
    if use_terms:
        term = program_evaluation_json.TERM
        assert code.count(term) == 1
        raw = re.sub(r'\bjterm\b', 'jterm_raw', term)
        wrapper = r'''
fun jterm term = let
  val (index,next) = N.complete_term_reference term (!native_term_rows);
  val size = length next;
  val () = native_term_rows := next;
  val () = if size > !native_term_count then
      (native_term_count := size;
       print ("NATIVE_TERM_VALUE " ^ jnat index ^ " " ^ jterm_raw term ^ "\n"))
    else ();
  in "{\"__native_complete_term__\":" ^ jnat index ^ "}" end;
'''
        code = code.replace(term, raw + wrapper, 1)
    return code


def artifact(value):
    if not isinstance(value, dict) or set(value) != FIELDS:
        raise ValueError('Incomplete artifact transport value.')

    if not isinstance(value['carrier'], list) or not all(map(word, value['carrier'])):
        raise ValueError('Invalid artifact carrier transport.')
    for field, width in [('incidence', 3), ('counted_data', 2), ('functional_data', 2)]:
        if not isinstance(value[field], list) or not all(
                isinstance(row, list) and len(row) == width and all(map(word, row))
                for row in value[field]):
            raise ValueError('Invalid artifact field transport: ' + field)


def term(value):
    pending = [value]
    while pending:
        node = pending.pop()
        if not isinstance(node, dict) or len(node) != 1:
            raise ValueError('Invalid complete term transport.')
        if 'payload' in node and word(node['payload']):
            continue
        if 'pair' in node and isinstance(node['pair'], list) and len(node['pair']) == 2:
            pending.extend(node['pair'])
            continue
        target = node.get('target')
        if isinstance(target, dict) and len(target) == 1:
            if 'whole_artifact' in target:
                artifact(target['whole_artifact'])
                continue
            anchored = target.get('anchored_artifact')
            if isinstance(anchored, list) and len(anchored) == 2 and word(anchored[1]):
                artifact(anchored[0])
                continue
        raise ValueError('Invalid complete term transport.')


def clone(value):
    """Copy a decoded term without imposing another recursive depth boundary."""
    result = [None]
    pending = [(result, 0, value)]
    while pending:
        parent, key, item = pending.pop()
        if isinstance(item, dict):
            output = {}
            parent[key] = output
            pending.extend((output, k, v) for k, v in reversed(list(item.items())))
        elif isinstance(item, list):
            output = [None] * len(item)
            parent[key] = output
            pending.extend((output, i, item[i]) for i in reversed(range(len(item))))
        else:
            parent[key] = item
    return result[0]


class Decoder:
    """Recover complete records, with explicit ordered dictionary and end boundaries."""
    def __init__(self):
        self.active = False
        self.finished = False
        self.table = []
        self.used = set()
        self.version = None
        self.terms = []
        self.terms_used = set()
        self.artifact_bytes = []
        self.term_bytes = []
        self.artifact_values = []
        self.term_values = []
        self.footer_loaded = False

    def reference(self, value):
        marker = REFERENCE if REFERENCE in value else TERM_REFERENCE if TERM_REFERENCE in value else None
        if marker is None:
            return None
        table, used, encoded = ((self.table, self.used, self.artifact_bytes) if marker == REFERENCE
                               else (self.terms, self.terms_used, self.term_bytes))
        if marker == TERM_REFERENCE and self.version not in [2, 3]:
            raise ValueError('Term reference outside version 2 transport.')
        i = value[marker]
        if set(value) != {marker} or type(i) is not int or not 0 <= i < len(table):
            raise ValueError('Invalid complete artifact reference.')
        used.add(i)
        return table, encoded, i

    def validate_object(self, value):
        self.reference(value)
        return value

    def object(self, value):
        """Resolve a dictionary during the existing bottom-up JSON parse."""
        reference = self.reference(value)
        if reference is None:
            return value
        table, _, i = reference
        return self.occurrence(table, self.artifact_values if REFERENCE in value else self.term_values, i)

    @staticmethod
    def occurrence(table, encodings, i):
        """Give one occurrence its own complete mutable value, decoded from the entry's exact encoding.

        Parsing the retained insertion-order encoding reproduces every key order, number and nesting
        without sharing a container between occurrences. A value too deep for the JSON codec keeps
        the iterative copy.
        """
        while len(encodings) < len(table):
            try:
                encodings.append(json.dumps(table[len(encodings)], ensure_ascii=False,
                                            separators=(',', ':'), allow_nan=False))
            except RecursionError:
                encodings.append(None)
        if encodings[i] is not None:
            try:
                return json.loads(encodings[i])
            except RecursionError:
                pass
        return clone(table[i])

    def canonical_chunks(self, value):
        pending = [(False, value)]
        while pending:
            encoded, item = pending.pop()
            if encoded:
                yield item
            elif isinstance(item, dict):
                reference = self.reference(item)
                if reference is not None:
                    _, data, i = reference
                    yield data[i]
                else:
                    parts = [(True, b'{')]
                    for i, (key, entry) in enumerate(sorted(item.items())):
                        if i:
                            parts.append((True, b','))
                        parts.extend([(True, json.dumps(key, ensure_ascii=True).encode('utf-8')),
                                      (True, b':'), (False, entry)])
                    parts.append((True, b'}'))
                    pending.extend(reversed(parts))
            elif isinstance(item, list):
                parts = [(True, b'[')]
                for i, entry in enumerate(item):
                    if i:
                        parts.append((True, b','))
                    parts.append((False, entry))
                parts.append((True, b']'))
                pending.extend(reversed(parts))
            else:
                yield json.dumps(item, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('utf-8')

    def field(self, value, path, *, resolve_final=True):
        for key in path:
            if isinstance(value, dict):
                reference = self.reference(value)
                if reference is not None:
                    table, _, i = reference
                    value = table[i]
            value = value[key]
        if resolve_final and isinstance(value, dict):
            reference = self.reference(value)
            if reference is not None:
                table, _, i = reference
                value = table[i]
        return value

    def expand(self, value):
        result = [None]
        pending = [(result, 0, value)]
        while pending:
            parent, key, item = pending.pop()
            if isinstance(item, dict):
                if REFERENCE in item or TERM_REFERENCE in item:
                    # Preserve the original reader's independent mutable JSON occurrences.
                    # Native dictionary sharing must not allow a caller to mutate later records.
                    parent[key] = self.object(item)
                else:
                    output = {}
                    parent[key] = output
                    pending.extend((output, k, v) for k, v in reversed(list(item.items())))
            elif isinstance(item, list):
                output = [None] * len(item)
                parent[key] = output
                pending.extend((output, i, item[i]) for i in reversed(range(len(item))))
            else:
                parent[key] = item
        return result[0]

    def read(self, row, *, expanded=False):
        tag, indices, value = row['tag'], row['indices'], row['value']
        if tag in [ARTIFACT_TABLE, TERM_TABLE]:
            raise ValueError('Native dictionary table outside the footer protocol.')
        if tag == BEGIN:
            if (self.active or indices or not isinstance(value, dict)
                    or set(value) != {'version'} or type(value['version']) is not int or value['version'] not in [1, 2, 3]):
                raise ValueError('Invalid artifact stream start.')
            self.active = True
            self.version = value['version']
            return None
        if tag in [ENTRY, TERM_ENTRY, END]:
            if not self.active or self.finished:
                raise ValueError('Artifact stream entry outside its boundary.')
            if tag == ENTRY:
                if indices != [len(self.table)]:
                    raise ValueError('Artifact stream dictionary is not an exact append.')
                artifact(value)
                self.table.append(value)
                self.artifact_bytes.append(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('utf-8'))
            elif tag == TERM_ENTRY:
                if self.version not in [2, 3] or indices != [len(self.terms)]:
                    raise ValueError('Term dictionary is not an exact append.')
                term(value)
                self.terms.append(value)
                self.term_bytes.append(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('utf-8'))
            else:
                fields = {'entries'} if self.version == 1 else {'entries', 'terms'}
                if (indices or not isinstance(value, dict) or set(value) != fields
                        or type(value['entries']) is not int or value['entries'] != len(self.table)
                        or self.used != set(range(len(self.table)))
                        or (self.version in [2, 3] and (type(value['terms']) is not int
                            or value['terms'] != len(self.terms) or self.terms_used != set(range(len(self.terms)))))):
                    raise ValueError('Incomplete artifact stream coverage.')
                self.finished = True
            return None
        if self.finished:
            raise ValueError('Native report after artifact stream completion.')
        return {**row, 'value': self.expand(value)} if self.active and not expanded else row

    def finish(self):
        if self.active and not self.finished:
            raise ValueError('Truncated artifact stream.')

    def load_tables(self, artifacts, terms):
        if (not self.active or self.finished or self.version != 3 or self.footer_loaded
                or not isinstance(artifacts, list) or not isinstance(terms, list)):
            raise ValueError('Incomplete native dictionary tables.')
        self.footer_loaded = True
        for i, value in enumerate(artifacts):
            self.read({'tag': ENTRY, 'indices': [i], 'value': value})
        for i, value in enumerate(terms):
            self.read({'tag': TERM_ENTRY, 'indices': [i], 'value': self.expand(value)}, expanded=True)
