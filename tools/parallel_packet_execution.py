"""Execute original packets through proved sharing and Isabelle parallel maps."""
from pathlib import Path
import argparse
import json
import time
import resource

ROOT = Path(__file__).resolve().parents[1]

import check_constructed_history
import check_streamed_digit_replay
import compressed_native_execution
import execution_support as investigate
import observation_contracts
import shared_artifact_reports
import shared_object_stream
import derived_observation_stream
import projected_source_stream
from evidence_io import digest, write_json

def main(entrypoint, *, kind, root):
    parser = argparse.ArgumentParser(description='Execute a complete proved packet using independent native tasks.')
    parser.add_argument('--proof', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--poly', type=Path, required=True)
    parser.add_argument('--project', type=Path, default=ROOT)
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--cases', type=int, nargs='+')
    parser.add_argument('--workers', type=int, default=16)
    args = parser.parse_args()
    assert 1 <= args.workers <= 16
    isabelle = Path('/opt/isabelle/bin/isabelle')
    pure = Path('/opt/isabelle/heaps/polyml-5.9.2_x86_64_32-linux/Pure')
    assert args.poly.resolve() == Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
    assert args.timeout > 0
    runtime_inputs = [pure,
        isabelle, Path('/usr/bin/env'),
        Path('/opt/isabelle/src/Pure/ML/ml_process.scala'),
        Path('/opt/isabelle/src/Pure/ML/ml_statistics.ML'),
        Path('/opt/isabelle/src/HOL/Library/Parallel.thy'),
        Path('/opt/isabelle/src/Pure/Concurrent/par_list.ML'),
        Path('/opt/isabelle/src/Pure/Concurrent/future.ML'),
        Path('/opt/isabelle/src/Pure/Concurrent/task_queue.ML'),
        Path('/opt/isabelle/src/Pure/Concurrent/multithreading.ML'),
        Path('/opt/isabelle/contrib/polyml-5.9.2-2/etc/settings')]
    proof = json.loads(args.proof.read_text())
    assert proof['export_theory'] == root
    assert len(proof['subject_contracts']) == 1
    entry = proof['subject_contracts'][0]
    assert investigate.file_hash(Path(entry['path'])) == entry['sha256']
    if kind == 'replay':
        theory, definition, prefix = 'Factor_Digit_Replay_Investigation', 'digit_replay_investigation', 'DIGIT_REPLAY'
        base_program, packet, introductory = check_streamed_digit_replay.program, 'digit_replay_packet', ('SEEDS', 'PREVIOUS_SOURCES')
    else:
        theory, definition, prefix = 'Factor_Constructed_History_Investigation', 'constructed_history_investigation', 'CONSTRUCTED_HISTORY'
        base_program, packet, introductory = check_constructed_history.program, 'constructed_history_packet', ()
    contract = observation_contracts.read_contract(Path(entry['path']), theory, definition,
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')


    def program(engine, inputs):
        code = 'val print = fn text => TextIO.output (TextIO.stdOut, text);\nval artifact_reporting_clock = ref (Timer.startRealTimer ());\n' + base_program(engine, inputs)
        code = derived_observation_stream.program(code, kind=kind)
        code = projected_source_stream.program(code, kind=kind)
        before = 'val (table,(comparison,cycles)) = N.' + packet + ' scope selections;'
        assert code.count(before) == 1
        timing = r"""
    fun stage_timed label thunk = let
      val () = print ("Physicalstart " ^ label ^ "\n");
      val () = TextIO.flushOut TextIO.stdOut;
      val timer = Timer.startRealTimer ();
      val cpu_timer = Timer.startCPUTimer ();
      val before_stats = ML_Statistics.get ();
      val result = thunk ();
      val {usr,sys} = Timer.checkCPUTimer cpu_timer;
      val gc_time = Timer.checkGCTime cpu_timer;
      val after_stats = ML_Statistics.get ();
      val () = print ("Physicaltime " ^ label ^ " " ^
        LargeInt.toString (Time.toMilliseconds (Timer.checkRealTimer timer)) ^ "ms\n");
      val () = print ("Physicalcpu " ^ label ^ " user_ms=" ^ LargeInt.toString (Time.toMilliseconds usr) ^
        " system_ms=" ^ LargeInt.toString (Time.toMilliseconds sys) ^
        " gc_ms=" ^ LargeInt.toString (Time.toMilliseconds gc_time) ^ "\n");
      val () = print ("Physicalstats-before " ^ label ^ " " ^
        String.concatWith " " (map (fn (key,value) => key ^ "=" ^ value) before_stats) ^ "\n");
      val () = print ("Physicalstats-after " ^ label ^ " " ^
        String.concatWith " " (map (fn (key,value) => key ^ "=" ^ value) after_stats) ^ "\n");
      val () = TextIO.flushOut TextIO.stdOut;
      in result end;
    """
        native = kind + '_stage_'
        stages = ('val table = stage_timed "table" (fn () => N.' + native + 'table scope);\n'
            'val comparison = stage_timed "comparison" (fn () => N.' + native + 'compare scope table);\n'
            'val cycles = stage_timed "cycles" (fn () => N.' + native + 'cycles comparison selections);\n'
            'val () = artifact_reporting_clock := Timer.startRealTimer ();\n')
        code = code.replace(before, timing + 'val () = print (\"Physicalworkers \" ^ Int.toString (Multithreading.max_threads ()) ^ \"\\n\");\n' + stages)
        code = shared_object_stream.program_with_references(code, prefix)
        assert code.count('= ref ') == 2
        code = code.replace('= ref ', '= Unsynchronized.ref ')
        return code + '''
    val () = print ("Physicaltime reporting " ^ LargeInt.toString
      (Time.toMilliseconds (Timer.checkRealTimer (!artifact_reporting_clock))) ^ "ms\\n");
    val () = TextIO.flushOut TextIO.stdOut;
    '''


    cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    result = compressed_native_execution.checked_execution(args.proof,
        args.poly.resolve(), args.output, workers=args.workers, runtime_target='Eval',
        required_theories=[root],
        inputs={'workers': args.workers, 'cases': args.cases, 'candidates': contract['candidate_indices'],
                'facets': contract['facet_indices'], 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), Path(entrypoint), Path(entry['path']), *runtime_inputs], program=program,
        assess=lambda inputs, path: shared_artifact_reports.assess(inputs, path,
            prefix=prefix, introductory=introductory), project=args.project.resolve(), timeout=args.timeout,
        question='Can the complete original packet execute and retain every value within the declared development-time budget?',
        boundary='The proved stages reconstruct the complete native packet and retain the original subject contract. Source projection reads actual stored contexts. The proved exact artifact-reference '
                 'operation retains every full artifact and every occurrence, including repeated counts. '
                 'The complete reference table accompanies the stored reports. Timers are physical metadata.')
    write_json(args.output / 'runtime-metadata.json', {'files': {name: digest(args.output / name) for name in ['runtime-command.json'] if (args.output / name).is_file()}, 'boundary': 'Physical runtime and garbage collection diagnostics; complete native stages reconstruct the original packet under their established equation.'})
    elapsed = time.monotonic() - started
    cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu_user = cpu_after.ru_utime - cpu_before.ru_utime
    cpu_system = cpu_after.ru_stime - cpu_before.ru_stime
    (args.output / 'physical-runtime.json').write_text(json.dumps({'seconds': elapsed, 'cpu_user_seconds': cpu_user, 'cpu_system_seconds': cpu_system,
        'average_cpu_cores_including_startup_and_retention': (cpu_user + cpu_system) / elapsed,
        'scope': args.cases, 'status': result['status'], 'boundary': 'Complete execution and retention elapsed time.'}) + '\n')
    print(json.dumps({'status': result['status'], 'error': result.get('error'), 'seconds': elapsed,
                      'reports': result.get('assessment', {}).get('reproduction_boundary'),
                      'transport': result.get('assessment', {}).get('artifact_transport')}), flush=True)
    return int(result['status'] != 'accepted')
