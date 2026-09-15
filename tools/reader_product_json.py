"""Serialize a complete reader assessment paired with an additional observation."""
import reader_comparison_json


def prelude(value, context_writer, result_writer, inspector):
    original = reader_comparison_json.prelude(value, inspector)
    boundary = original.index('fun jquality')
    reader = original[:boundary].replace('fun jcontext', 'fun jreaderContext').replace('fun jresult', 'fun jreaderResult')
    return reader + r'''
fun jcontext (reader,additional) = "{\"reader\":" ^ jreaderContext reader ^
  ",\"additional\":" ^ __CONTEXT__ additional ^ "}";
fun jresult (reader,additional) = "{\"reader\":" ^ jreaderResult reader ^
  ",\"additional\":" ^ __RESULT__ additional ^ "}";
'''.replace('__CONTEXT__', context_writer).replace('__RESULT__', result_writer) + original[boundary:]
