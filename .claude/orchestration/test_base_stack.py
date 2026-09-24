"""Complete-load, source-boundary and suffix-rebuild controls for named bases; no real model is launched."""
import contextlib
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest
from unittest.mock import patch

import base_pack
import base_stack as stack
import manifest
import select_base_load as select
import v2
REAL_FORK=stack.fork


class StackTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.root=Path(self.temp.name)
        self.state=self.root/'state';self.state.mkdir()
        self.project=self.root/'project';self.project.mkdir()
        self.transcripts=self.root/'transcripts';self.transcripts.mkdir()
        self.list=self.root/'list.txt'
        self.list.write_text('# reference; purpose=steering\nreference.md\n# === layer direction ===\n'
                             '# direction; purpose=steering\ndirection.md\n# === layer catalogue ===\n'
                             '# discovery; purpose=steering\ncatalogue.md\n# === layer working ===\n'
                             '# supplied contracts; purpose=both\nworking.md\n')
        for name in ('reference','direction','catalogue','working'):
            (self.project/f'{name}.md').write_text(f'# {name}\nThe recorded material of {name}.\n')
        flags=' '.join(v2.session_flags())
        self.base=dict(sessionId='root',name='high-base',model=v2.base_model(),effort='high',flags=flags,context=10000,
                       prompt_sha256=hashlib.sha256((stack.HERE/'library-prompt.md').read_bytes()).hexdigest())
        self.base['stable_layout']=stack.fingerprint([('reference; purpose=steering',str(self.project/'reference.md'),'statements')])
        (self.state/'high-base.json').write_text(json.dumps(self.base))
        (self.state/'high-manifest.json').write_text(json.dumps({'files':{str(self.project/'reference.md'):'root'}}))
        (self.state/'high-stable.hit').touch()
        self.calls=[];self.incomplete=False;self.reason_tool=False;self.reason_done=True
        self.thought=20000;self.carried=20000
        self.patches=contextlib.ExitStack()
        for obj,key,value in ((stack,'STATE',self.state),(stack,'PROJECT',self.project),(v2,'STATE',str(self.state)),
                              (v2,'PROJECT',str(self.project)),(v2,'control',lambda:True),
                              (v2,'transcript',lambda sid:str(self.transcripts/f'{sid}.jsonl')),
                              (v2,'context_of',lambda sid:10000+len(self.calls)*1000),
                              (v2,'claude',lambda *a,**k:subprocess.CompletedProcess(a,0,'','')),
                              (stack,'fork',self.fork),(select,'frontier',lambda who:0),
                              (select,'refresh_indexes',lambda who=None:0),(select,'projection',lambda who:dict(room_before_reasoning=500000))):
            self.patches.enter_context(patch.object(obj,key,value))
        self.patches.enter_context(patch.dict(os.environ,ORCH_PROJECT=str(self.project),ORCH_STATE_DIR=str(self.state),
                                             ORCH_LOAD_LIST=str(self.list),BASE_LOAD_LIST=str(self.list)))

    def tearDown(self):
        self.patches.close();self.temp.cleanup()

    def fork(self,parent,name,prompt):
        part='reasoning' if '-reasoning-' in name else name.split('-')[1]
        self.calls.append((part,parent['sessionId']))
        sid='s'+str(len(self.calls));now=time.time()
        stamp=datetime.datetime.fromtimestamp(now+0.01,datetime.timezone.utc).isoformat()
        records=[]
        if part=='reasoning':
            content=[{'type':'text','text':stack.DONE if self.reason_done else 'not complete'}]
            if self.reason_tool:content.append({'type':'tool_use','id':'forbidden','name':'Bash','input':{'command':'true'}})
            records.append({'type':'assistant','timestamp':stamp,'message':{'id':'m-'+sid,'content':content,
                            'usage':{'input_tokens':int(parent.get('context') or 0),'output_tokens':self.thought}}})
        else:
            packed=max(self.state.glob('base-pack-*'),key=lambda p:p.stat().st_mtime_ns)
            meta=base_pack.verify(packed)
            for i,text in enumerate(base_pack.checked_chunks(packed,meta),1):
                if self.incomplete and part=='working':continue
                records.append({'type':'user','timestamp':stamp,'message':{'content':[
                    {'type':'tool_result','content':base_pack.envelope(meta,i,text),'tool_use_id':str(i)}]}})
            under=int(parent.get('context') or 0)+(self.carried if parent.get('kind')=='reasoning' else 0)
            records.append({'type':'assistant','timestamp':stamp,'message':{'id':'m-'+sid,'content':[
                {'type':'text','text':'LOADED '+meta['id']}],'usage':{'input_tokens':under+300,'output_tokens':5}}})
        (self.transcripts/f'{sid}.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records))
        return dict(name=name,sid=sid,id=sid,activity='idle'),now

    def test_complete_chain_reuses_unchanged_parts_and_rebuilds_only_dependent_suffix(self):
        first=stack.build('high')
        self.assertEqual([p['part'] for p in first['parts']],['stable','reasoning','direction','catalogue','working'])
        self.assertEqual(first['parent'],first['parts'][-2]['sessionId'])
        self.assertEqual(stack.build('high')['sessionId'],first['sessionId'])
        self.assertEqual(len(self.calls),4)
        (self.project/'working.md').write_text('Changed working contract.\n')
        second=stack.build('high')
        self.assertEqual(self.calls[-1][0],'working')
        self.assertEqual(len(self.calls),5)
        self.assertEqual(second['parts'][1]['sessionId'],first['parts'][1]['sessionId'])
        (self.project/'direction.md').write_text('A changed owner direction.\n')
        stack.build('high')
        self.assertEqual([c[0] for c in self.calls[-3:]],['direction','catalogue','working'])
        self.assertEqual(len(self.calls),8)

    def test_incomplete_load_keeps_the_published_chain_and_releases_the_lock(self):
        first=stack.build('high')
        (self.project/'working.md').write_text('A different contract.\n')
        self.incomplete=True
        with self.assertRaises(RuntimeError):stack.build('high')
        self.assertEqual(stack.read(self.state/'high-layer.json')['sessionId'],first['sessionId'])
        self.assertFalse((self.state/'high-layer.building').exists())

    def test_a_failed_build_leaves_the_published_list_as_it_was_and_a_published_one_installs_it(self):
        stack.build('high')
        before=self.list.read_text()
        def regenerate(who):
            path=Path(select.list_path(who))
            self.assertNotEqual(path,self.list)  # a build writes its candidate, never the published list
            path.write_text(path.read_text()+'# a newly generated tier\n')
        (self.project/'working.md').write_text('A different contract.\n')
        self.incomplete=True
        with patch.object(select,'frontier',regenerate):
            with self.assertRaises(RuntimeError):stack.build('high')
            self.assertEqual(self.list.read_text(),before)
            self.assertEqual(list(self.state.glob('high-load-next.txt*')),[])
            self.incomplete=False
            stack.build('high')
        self.assertEqual(self.list.read_text(),before+'# a newly generated tier\n')
        self.assertEqual(os.environ.get('BASE_LOAD_LIST'),str(self.list))

    def test_the_queue_is_no_reason_to_rebuild_but_an_edit_of_the_list_is(self):
        stack.build('high')
        with patch.object(select,'relation_choice',side_effect=AssertionError('the queue decides nothing here')):
            self.assertIsNone(stack.refresh_reason('high'))
            (self.project/'rules.md').write_text('A rule the owner added.\n')
            self.list.write_text(self.list.read_text().replace('direction.md\n','direction.md\nrules.md\n'))
            self.assertIn("direction part holds other entries",stack.refresh_reason('high'))

    def test_reasoning_that_fails_twice_over_the_same_reference_is_the_owners(self):
        self.reason_done=False
        stack.build('high')
        self.assertIsNone(stack.refresh_reason('high'))  # the automatic retry waits its interval
        with patch.object(v2,'RETRY',0):
            self.assertIn('reasoning',stack.refresh_reason('high'))
            stack.build('high')
            self.assertEqual(stack.read(self.state/'high-reasoning-failed.json')['count'],2)
            with patch.object(v2,'say_once') as said:
                self.assertIsNone(stack.refresh_reason('high'))
            self.assertIn('failed twice',said.call_args.args[1])
        self.reason_done=True
        self.assertEqual(stack.build('high')['reasoning_status'],'complete')  # the owner's build tries again
        self.assertFalse((self.state/'high-reasoning-failed.json').exists())

    def test_whether_the_reasoning_is_carried_into_its_forks_is_measured(self):
        result=stack.build('high')
        seen=result['parts'][2]['over_reasoning']
        self.assertEqual(seen['thought'],20000)
        self.assertGreaterEqual(seen['carried'],20000-300)
        self.assertEqual(result['reasoning_carried'],seen['carried'])
        (self.state/'high-reasoning.miss').touch()
        self.carried=0
        with patch.object(v2,'say_once') as said:
            result=stack.build('high')
        self.assertLess(result['reasoning_carried'],10000)
        self.assertIn('not carried into its forks',said.call_args.args[1])

    def test_each_part_a_refresh_may_start_from_is_priced_by_what_it_loads_again(self):
        result=stack.build('high')
        c={p['part']:p['context'] for p in result['parts']}
        top=c['working']
        # the stable part loaded again with everything over it; a named part over one read of what stands under it
        self.assertEqual(stack.suffix_costs('high'),[('stable',top,0),('direction',top-c['reasoning'],c['reasoning']),
                         ('catalogue',top-c['direction'],c['direction']),('working',top-c['catalogue'],c['catalogue'])])

    def test_a_refresh_from_a_part_keeps_the_parts_under_it_whatever_changed_in_them(self):
        # each part on its own schedule (the owner, 2026-09-23): an appended decision under a rewritten top part is
        # carried by the delta until carrying it has cost what loading its part again costs, then consolidated
        first=stack.build('high')
        (self.project/'direction.md').write_text('A decision appended.\n')
        (self.project/'working.md').write_text('A rewritten working contract.\n')
        second=stack.build('high','working')
        self.assertEqual([c[0] for c in self.calls[4:]],['working'])
        self.assertEqual(second['parts'][2]['sessionId'],first['parts'][2]['sessionId'])   # direction, as it loaded
        stack.build('high','direction')
        self.assertEqual([c[0] for c in self.calls[5:]],['direction','catalogue','working'])
        # a refresh from a part reaches the builder from base.sh
        self.assertIn('build "$who" ${3:+"$3"} ${4:+"$4"}',(stack.HERE/'base.sh').read_text())

    def test_each_build_reads_what_claude_code_put_into_the_reference(self):
        import window_watch
        with patch.object(window_watch, "audit_openings") as audit:
            stack.build('high')
        audit.assert_called_once()

    def test_the_watchdog_prices_a_chain_refresh_by_what_it_rebuilds(self):
        import watchdog
        result=stack.build('high')
        (self.project/'working.md').write_text('Changed.\n')
        contexts={p['part']:p['context'] for p in result['parts']}
        with patch.object(watchdog,'STATE',str(self.state)),patch.object(v2,'role_layers',return_value=[]):
            cost=watchdog.refresh_cost('high')
        self.assertAlmostEqual(cost,2*(contexts['working']-contexts['catalogue'])+0.1*contexts['catalogue'])

    def test_a_list_that_cannot_be_built_is_said_and_not_rebuilt_every_minute(self):
        stack.build('high')
        (self.project/'direction.md').unlink()
        with patch.object(v2,'say_once') as said:
            self.assertIsNone(stack.refresh_reason('high'))
        self.assertIn('cannot be built as it stands',said.call_args.args[1])

    def test_reasoning_with_a_tool_is_not_certified_and_its_material_parent_is_used(self):
        self.reason_tool=True
        result=stack.build('high')
        self.assertEqual(result['reasoning_status'],'failed: parent fallback')
        self.assertEqual(result['parts'][1]['parent'],'root')
        self.assertFalse((self.state/'high-reasoning.json').exists())

    def test_cold_reasoning_rebuilds_it_and_its_suffix_not_the_stable_source(self):
        first=stack.build('high')
        (self.state/'high-reasoning.miss').touch()
        count=len(self.calls)
        second=stack.build('high')
        self.assertEqual(len(self.calls),count+4)
        self.assertNotEqual(first['sessionId'],second['sessionId'])
        self.assertEqual([c[0] for c in self.calls[-4:]],['reasoning','direction','catalogue','working'])
        self.assertEqual(self.calls[-4][1],'root')
        self.assertEqual(stack.read(self.state/'high-base.json')['sessionId'],'root')

    def test_parent_identity_is_part_of_reuse_and_a_broken_published_chain_is_refused(self):
        first=stack.build('high')
        cached=stack.read(stack.record_path('high','catalogue'));cached['parent']='another-direction'
        stack.write(stack.record_path('high','catalogue'),cached)
        count=len(self.calls)
        stack.build('high')
        self.assertEqual(len(self.calls),count+2)
        self.assertIsNotNone(v2.layer_record('high'))
        self.assertEqual([c[0] for c in self.calls[-2:]],['catalogue','working'])
        broken=stack.read(self.state/'high-layer.json');broken['parts'][2]['parent']='wrong-root'
        stack.write(self.state/'high-layer.json',broken)
        self.assertIsNone(v2.layer_record('high'))

    def test_a_launch_hold_starts_nothing(self):
        (self.state/'no-launch').write_text('owner hold')
        with self.assertRaisesRegex(RuntimeError,'hold'):stack.build('high')
        self.assertEqual(self.calls,[])

    def test_every_snapshot_contains_its_actual_ancestors(self):
        result=stack.build('high')
        for i,part in enumerate(result['parts'][2:],1):
            files=stack.read(part['snapshot'])['files']
            self.assertIn(str(self.project/'reference.md'),files)
            self.assertIn(str(self.project/'direction.md'),files)
            self.assertEqual(len(files),i+1)

    def test_missing_required_material_is_not_silently_left_out(self):
        (self.project/'direction.md').unlink()
        with self.assertRaisesRegex(FileNotFoundError,'Required base source'):stack.build('high')
        self.assertEqual(self.calls,[])

    def test_reasoning_requires_its_own_completion_not_an_inherited_reply(self):
        import watchdog
        with patch.object(watchdog,'last_reply',return_value=('',stack.DONE,time.time()-100)):
            result=stack.build('high')
        self.assertEqual(result['reasoning_status'],'failed: parent fallback')
        self.assertFalse((self.state/'high-reasoning.json').exists())

    def test_the_reuse_identity_is_the_actual_frozen_content(self):
        original=stack.load_part
        def change_before_freeze(who,description,parent,snapshot):
            if description['part']=='working':
                (self.project/'working.md').write_text('Changed after selection, before the pack froze.\n')
            return original(who,description,parent,snapshot)
        with patch.object(stack,'load_part',side_effect=change_before_freeze):
            first=stack.build('high')
        count=len(self.calls)
        self.assertEqual(stack.build('high')['sessionId'],first['sessionId'])
        self.assertEqual(len(self.calls),count)

    def test_a_candidate_hit_does_not_warm_the_older_published_entry(self):
        result=stack.build('high')
        old=result['parts'][-1]
        stack.touch('high','working','another-candidate')
        self.assertTrue(stack.warm('high','working',old))
        own=self.state/'entry-hits'/old['sessionId']
        os.utime(own,(time.time()-2*v2.WARM_MAX,)*2)
        stack.touch('high','working','another-candidate')
        self.assertFalse(stack.warm('high','working',old))

    def test_repeated_layer_names_cannot_reorder_material_silently(self):
        self.list.write_text(self.list.read_text()+'# === layer direction ===\n# later direction\nworking.md\n')
        with self.assertRaisesRegex(ValueError,'distinct'):stack.build('high')
        self.assertEqual(self.calls,[])

    def test_changed_reference_depth_requires_a_reference_reload(self):
        self.list.write_text(self.list.read_text().replace('# reference; purpose=steering',
                                                         '# reference; purpose=steering; as definitions'))
        original=stack.checked
        def stop_at_reload(*args,**kwargs):
            if args[0]=='sh' and args[-1]=='restable':raise RuntimeError('reference reload required')
            return original(*args,**kwargs)
        with patch.object(stack,'checked',side_effect=stop_at_reload):
            with self.assertRaisesRegex(RuntimeError,'reference reload required'):stack.build('high')
        self.assertEqual(self.calls,[])

    def test_a_refresh_from_the_stable_part_loads_the_reference_again(self):
        # the owner, 2026-09-23: the stable part's reload follows the rule automatically once its account has paid
        stack.build('high')
        original=stack.checked
        def stop_at_reload(*args,**kwargs):
            if args[0]=='sh' and args[-1]=='restable':raise RuntimeError('reference reload required')
            return original(*args,**kwargs)
        with patch.object(stack,'checked',side_effect=stop_at_reload):
            stack.build('high','working')                                  # a refresh over it keeps the reference
            with self.assertRaisesRegex(RuntimeError,'reference reload required'):stack.build('high','stable')

    def test_a_reference_built_on_another_model_is_loaded_again(self):
        # every fork takes its origin's model: a stable base left from Claude Opus 5 would carry it to every session
        (self.state/'high-base.json').write_text(json.dumps(dict(self.base,model='claude-opus-5[1m]')))
        original=stack.checked
        def stop_at_reload(*args,**kwargs):
            if args[0]=='sh' and args[-1]=='restable':raise RuntimeError('reference reload required')
            return original(*args,**kwargs)
        with patch.object(stack,'checked',side_effect=stop_at_reload):
            with self.assertRaisesRegex(RuntimeError,'reference reload required'):stack.build('high')
        self.assertEqual(self.calls,[])

    def test_reference_builder_uses_the_registered_inert_launcher(self):
        rec=dict(origin_sid='root',sid='guarded',id='guarded',started=time.time())
        row=dict(name='reference-guarded',sid='guarded',id='guarded')
        with patch.object(v2,'launch',return_value='reference-guarded') as launch, \
                patch.object(v2,'peek',return_value={'sessions':{'reference-guarded':rec}}), \
                patch.object(v2,'fork',side_effect=AssertionError('An unregistered reasoning fork is forbidden')), \
                patch.object(stack,'wait_for',return_value=row):
            result,_=REAL_FORK(self.base,'high-reasoning-test','reason from the reference')
        self.assertEqual(result['sid'],'guarded')
        self.assertEqual(launch.call_args.args[0],'base-reasoning')
        self.assertEqual(launch.call_args.kwargs['origin'],'high:stable')

    def test_an_unknown_context_size_is_not_published_as_zero(self):
        with patch.object(v2,'context_of',return_value=0):
            with self.assertRaisesRegex(RuntimeError,'size is unavailable'):stack.build('high')
        self.assertFalse((self.state/'high-layer.json').exists())


class RolePlacementTests(unittest.TestCase):
    def test_task_is_returned_for_resizing_before_an_oversized_fork(self):
        state={'sessions':{},'tasks':{'7':{'stage':'ready'}},'events':[]}
        @contextlib.contextmanager
        def stored():yield state
        origin=dict(sid='large',model='m',effort='high',flags=' '.join(v2.session_flags()),context=850000)
        with patch.object(v2,'age_of',return_value=None),patch.object(v2,'role_churn_of',return_value='own'), \
                patch.object(v2,'origin_of',return_value=('own',origin)),patch.object(v2,'warm',return_value=True), \
                patch.object(v2,'read_task',return_value={'description':'Size: about 120K tokens of work'}), \
                patch.object(v2,'state',stored),patch.object(v2,'peek',return_value=state),patch.object(v2,'log'), \
                patch.object(v2,'fork') as fork:
            self.assertIsNone(v2.launch('implementer','7',lambda _:''))
        fork.assert_not_called()
        self.assertEqual(state['tasks']['7']['stage'],'planner')
        self.assertIn('actual prefix',state['events'][0]['text'])

    def launched(self,role,task,context,given=0):
        """Whether launch forks a session for task 7 (whose brief says 120K) from a prefix of `context` tokens."""
        state={'sessions':{},'tasks':{'7':task},'events':[]}
        @contextlib.contextmanager
        def stored():yield state
        origin=dict(sid='large',model='m',effort='high',flags=' '.join(v2.session_flags()),context=context)
        with tempfile.TemporaryDirectory() as temp, patch.object(v2,'STATE',temp), \
                patch.object(v2,'age_of',return_value=None),patch.object(v2,'role_churn_of',return_value='own'), \
                patch.object(v2,'origin_of',return_value=('own',origin)),patch.object(v2,'warm',return_value=True), \
                patch.object(v2,'read_task',return_value={'description':'Size: about 120K tokens of work'}), \
                patch.object(v2,'state',stored),patch.object(v2,'peek',return_value=state),patch.object(v2,'log'), \
                patch.object(v2,'held_back',return_value=''),patch.object(v2,'fork',return_value=None) as fork:
            v2.launch(role,'7',lambda _:'',tree=None,relations_tokens=given)
        return fork.called,state

    def test_a_fix_and_a_begun_task_are_never_handed_back_for_resizing(self):
        # a fix works on built work: the brief's Size is not its size, and a task half made is continued, never
        # returned to the planner, where nothing moves it (the review of 2026-09-23)
        for task in ({'stage':'fixing','session':'implement-7'},{'stage':'fixing'}):
            forked,state=self.launched('fixer',task,850000)
            self.assertTrue(forked)
            self.assertEqual(state['tasks']['7']['stage'],'fixing')
        forked,state=self.launched('implementer',{'stage':'running','session':'implement-7'},850000)
        self.assertTrue(forked)
        self.assertEqual(state['tasks']['7']['stage'],'running')

    def test_the_relations_a_task_is_given_come_out_of_its_room(self):
        context=v2.SOFT-v2.PROTOCOL_ROOM-150000  # 150K of room for the brief's 120K
        forked,state=self.launched('implementer',{'stage':'ready'},context)
        self.assertTrue(forked)
        forked,state=self.launched('implementer',{'stage':'ready'},context,given=100000)
        self.assertFalse(forked)
        self.assertEqual(state['tasks']['7']['stage'],'planner')
        self.assertIn('100K of its own relations',state['events'][0]['text'])

    def test_a_judging_roles_reasoning_stands_on_the_delta_warm_or_cold(self):
        with patch.object(v2,'deltas_on',return_value=True),patch.object(v2,'delta_record',return_value={'sessionId':'delta'}), \
                patch.object(v2,'entry_cold',return_value=True), \
                patch.object(v2,'base_record',side_effect=lambda who:(who,{'sid':who+'-delta'})), \
                patch.object(v2,'medium_record',side_effect=lambda who:(who+':layer',{'sid':who+'-material'})):
            self.assertEqual(v2.role_layer_origin('reviewer')[1]['sid'],'xhigh-delta')
            asked=[]
            with patch.object(v2,'age_of',return_value=None),patch.object(v2,'log'), \
                    patch.object(v2,'base_file',return_value='/state/xhigh-delta.json'), \
                    patch.object(v2,'origin_of',side_effect=lambda o:(asked.append(o),(None,None))[1]):
                v2.launch('role-layer','reviewer',lambda _:'',tree=None,origin='xhigh',even_cold=True)
                v2.launch('implementer','8',lambda _:'',tree=None,origin='xhigh')
        # the reasoning is built over the delta even cold (it writes it once); a task's session forks the medium
        # layer rather than write a cold delta's whole prefix
        self.assertEqual(asked,['xhigh','xhigh:layer'])

    def test_a_reasoning_layers_thinking_is_part_of_the_room_its_forks_have(self):
        with patch.object(v2,'role_churn_of',return_value=None),patch.object(v2,'role_layer_of',return_value='own-layer'), \
                patch.object(v2,'peek',return_value={'sessions':{'own-layer':{'context':800000,'thought':30000}}}):
            self.assertEqual(v2.room_of('review'),max(0,v2.SOFT-830000-v2.PROTOCOL_ROOM))

    def test_reference_reasoning_is_inert_before_any_tool_executes(self):
        import fakes
        world=fakes.World()
        try:
            world.session('reference-one','base-reasoning','reference-sid')
            code,reply,error=world.hook('work_meter.py','guard',{
                'session_id':'reference-sid','cwd':str(world.project),'tool_name':'Bash','tool_input':{'command':'true'}})
            self.assertEqual(code,0,error)
            self.assertEqual(reply['hookSpecificOutput']['permissionDecision'],'deny')
        finally:
            world.close()

    def test_judgment_roles_reason_above_changes_and_execution_roles_below(self):
        with patch.object(v2,'deltas_on',return_value=True),patch.object(v2,'delta_record',return_value={'sessionId':'delta'}), \
                patch.object(v2,'entry_cold',return_value=False), \
                patch.object(v2,'base_record',side_effect=lambda who:(who,{'sid':who+'-delta'})), \
                patch.object(v2,'medium_record',side_effect=lambda who:(who+':layer',{'sid':who+'-material'})):
            for role in ('reviewer','designer','task-designer'):
                self.assertEqual(v2.role_layer_origin(role)[1]['sid'],'xhigh-delta')
            for role in ('implementer','fixer','investigator'):
                self.assertTrue(v2.role_layer_origin(role)[1]['sid'].endswith('-material'))

    def test_a_part_is_pinged_while_its_pings_since_its_use_cost_less_than_making_it_again(self):
        # the simulation of the run of 09-21/22: every part of every base pinged every forty minutes, 7M in fifteen
        # hours in which nothing read any of them; a cold intermediate part costs about one or two of its pings
        chain = [{'part': 'stable', 'sessionId': 's0', 'context': 300_000, 'sealed': '2026-09-23T10:00:00'},
                 {'part': 'reasoning', 'kind': 'reasoning', 'sessionId': 's1', 'context': 320_000, 'thought': 20_000},
                 {'part': 'direction', 'kind': 'material', 'sessionId': 's2', 'context': 350_000, 'model': 'm',
                  'effort': 'high'},
                 {'part': 'catalogue', 'kind': 'material', 'sessionId': 's3', 'context': 420_000}]
        with tempfile.TemporaryDirectory() as d:
            state = Path(d)

            def used(sid, ago):
                (state / 'entry-used').mkdir(exist_ok=True)
                p = state / 'entry-used' / sid
                p.write_text('')
                then = time.time() - ago
                os.utime(p, (then, then))
            with patch.object(stack, 'STATE', state), patch.object(v2, 'STATE', str(state)), \
                    patch.object(v2, 'layer_record', lambda who: {'parts': chain, 'context': 420_000}):
                used('s2', 60)
                self.assertTrue(stack.worth_keeping('high', 'direction', chain[2]))    # 35K a ping, 92K to make again
                used('s2', 2 * 2400 + 60)                                             # two pings since its use
                self.assertFalse(stack.worth_keeping('high', 'direction', chain[2]))
                used('s3', 10 * 3600)
                self.assertTrue(stack.worth_keeping('high', 'catalogue', chain[3]))    # the top: everything stands on it
                used('s0', 15 * 3600)                                                 # 23 pings, 690K: the chain 840K
                self.assertTrue(stack.worth_keeping('high', 'stable', chain[0]))
                used('s0', 30 * 3600)
                self.assertFalse(stack.worth_keeping('high', 'stable', chain[0]))
                (state / 'entry-used' / 's2').unlink()
                v2.hit('high:direction')                                               # a fork's read is a use
                self.assertTrue((state / 'entry-used' / 's2').exists())

    def test_a_part_not_worth_keeping_is_not_pinged(self):
        rec = {'sessionId': 's2', 'context': 350_000}
        forked = []

        def fork(*args):
            forked.append(args)
            raise RuntimeError('pinged')
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / 'entry-hits').mkdir()
            hit = Path(d) / 'entry-hits' / 's2'
            hit.write_text('')
            then = time.time() - 3000
            os.utime(hit, (then, then))
            with patch.object(stack, 'STATE', Path(d)), patch.object(stack, 'record', lambda who, part: rec), \
                    patch.object(stack, 'warm', lambda *a: True), patch.object(stack, 'fork', fork):
                with patch.object(stack, 'worth_keeping', lambda *a: False):
                    stack.ping('high', 'direction')
                self.assertEqual(forked, [])
                with patch.object(stack, 'worth_keeping', lambda *a: True), self.assertRaises(RuntimeError):
                    stack.ping('high', 'direction')                                   # due, and worth it: pinged

    def test_an_entry_is_warm_by_its_latest_read_under_either_of_its_marks(self):
        # the simulation of the run of 09-21/22: a stable base pinged every forty minutes (base.sh touches the part's
        # mark) looked cold at 56 by its own mark alone, set at its build, and was loaded again with its whole chain
        with tempfile.TemporaryDirectory() as d:
            state = Path(d)
            (state / 'entry-hits').mkdir()
            own = state / 'entry-hits' / 'sid-1'
            own.write_text('')
            old = time.time() - 2 * v2.WARM_MAX
            os.utime(own, (old, old))
            rec = {'sessionId': 'sid-1'}
            with patch.object(stack, 'STATE', state), patch.object(v2, 'other_tools', lambda rec: False):
                self.assertFalse(stack.warm('high', 'stable', rec))
                (state / 'high-stable.hit').write_text('sid-1')              # a ping's touch of the part's mark
                self.assertTrue(stack.warm('high', 'stable', rec))
                (state / 'high-stable.hit').write_text('sid-0')              # another session's: nothing of this one
                self.assertFalse(stack.warm('high', 'stable', rec))

    def test_old_reasoning_is_not_current_once_its_chain_is_replaced_and_no_churn_is_built_over_it(self):
        flags=' '.join(v2.session_flags())
        st={'sessions':{'review-reasoning':dict(layer_state='sealed',origin_sid='old-delta',flags=flags)},
            'role_layers':{'reviewer':{'name':'review-reasoning'}}}
        with patch.object(v2,'peek',return_value=st),patch.object(v2,'role_layers',return_value={'reviewer'}), \
                patch.object(v2,'warm',return_value=True),patch.object(v2,'deltas_on',return_value=False), \
                patch.object(v2,'role_layer_origin',return_value=('xhigh',{'sid':'new-delta'})):
            self.assertIsNone(v2.role_layer_of('reviewer'))
            self.assertIsNone(v2.role_churn_of('reviewer'))
            self.assertIn('replaced',v2.role_layer_due(st,'reviewer'))
            with patch.object(v2,'launch') as launch:
                v2.role_churn_care('reviewer',force=True)
                launch.assert_not_called()

    def test_task_room_uses_the_context_it_will_actually_fork(self):
        with patch.object(v2,'role_churn_of',return_value='own-churn'), \
                patch.object(v2,'peek',return_value={'sessions':{'own-churn':{'context':800000}}}):
            self.assertEqual(v2.room_of('build'),max(0,v2.SOFT-800000-v2.PROTOCOL_ROOM))


if __name__=='__main__':unittest.main()
