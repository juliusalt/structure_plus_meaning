"""Check complete paired projections, actual compiled clauses and source operands."""
from pathlib import Path
import argparse, itertools, json

import investigate, proved_code, check_reasoning as review
import check_keyed_tables as tables
import check_finite_inference as source_reader
from nonempty_source_case import ORIGINAL as SOURCE_SPEC


def inputs():
    p=review.payload
    pair=review.pair
    target={'empty_artifact':True}
    owner=p(3)
    row=lambda a,d,x,y:pair(pair(owner,a),pair(d,pair(x,y)))
    values=[p(7),target,pair(p(9),target)]
    rows=[row(p(i),p(11),x,y) for i,(x,y) in enumerate(itertools.product(values,repeat=2))]
    cases=[{'name':'empty','owner':owner,'rows':[]}]
    cases += [{'name':f'row-{i}','owner':owner,'rows':[r]} for i,r in enumerate(rows)]
    cases += [
        {'name':'complete-order','owner':owner,'rows':rows},
        {'name':'reverse-order','owner':owner,'rows':rows[::-1]},
        {'name':'repeated-occurrence','owner':owner,'rows':[rows[0],rows[0]]},
        {'name':'different-callees','owner':owner,'rows':[row(p(0),p(11),target,p(9)),row(p(1),p(12),target,p(9))]},
        {'name':'wrong-context','owner':p(4),'rows':[rows[0]]},
        {'name':'wrong-row-owner','owner':owner,'rows':[pair(pair(p(4),p(0)),pair(p(11),pair(target,p(9))))]},
        {'name':'missing-prefix','owner':owner,'rows':[pair(pair(owner,p(0)),pair(target,p(9)))]},
        {'name':'missing-pair','owner':owner,'rows':[pair(pair(owner,p(0)),p(7))]},
        {'name':'empty-malformed-context','owner':p(256),'rows':[]},
        {'name':'malformed-local-key','owner':owner,'rows':[row(p(256),p(11),target,p(9))]},
        {'name':'malformed-callee','owner':owner,'rows':[row(p(0),p(256),target,p(9))]},
        {'name':'malformed-first-observation','owner':owner,'rows':[row(p(0),p(11),p(256),p(9))]},
        {'name':'malformed-second-observation','owner':owner,'rows':[row(p(0),p(11),target,p(256))]},
        {'name':'malformed-tail','owner':owner,'rows':rows+[p(256)]},
        {'name':'formed-literal-context','owner':target,'rows':[]},
    ]
    large=[row(p(i//256,i%256),p(i%7),values[i%3],values[(i+1)%3]) for i in range(512)]
    cases += [{'name':'large-512','owner':owner,'rows':large},
              {'name':'large-512-reversed','owner':owner,'rows':large[::-1]}]
    return {'cases':cases,'source_payload':[],'source_spec':json.loads(SOURCE_SPEC.read_text()),
            'boundary':'All nine pairs over three declared complete values, all listed malformed-field controls, ordered/repeated rows and two 512-row traversals. This supplements the universal complete-input native contract.'}


def project(owner,rows):
    if not review.formed(owner):return None
    left,right=[],[]
    for r in rows:
        try:
            key,value=r['pair']
            actual,a=key['pair']
            d,xy=value['pair']
            x,y=xy['pair']
        except (KeyError,ValueError,TypeError):return None
        if actual!=owner or not all(review.formed(t) for t in [a,d,x,y]):return None
        left.append(review.pair(a,review.pair(d,x)))
        right.append(review.pair(a,review.pair(d,y)))
    return [left,right]


def expected_new_library():
    v=lambda i:{'var':i}
    p=review.pair
    seq=review.sequence
    def entry(d,head,premises):
        return {'entry':d,'schema':{'head':head,'premises':premises,'materials':[]},'enumeration':premises}
    root=lambda e,u,r:p(p(e,u),r)
    report=p(p(v(19),p(v(20),v(21))),p(v(22),p(v(23),v(24))))
    source=seq([root(v(0),v(1),v(2)),root(v(0),v(3),v(4)),p(v(5),v(6)),v(7),
                root(v(8),v(9),v(10)),v(11),p(v(12),report),v(14),v(15),v(16),v(17),v(18)])
    context=lambda u,a,b:p(u,p(a,b))
    reader=entry(359,p(source,v(13)),[
        [0,350,source],[1,21,v(13)],
        [2,28,context(p(v(3),v(4)),v(13),seq([p(p(v(5),v(6)),p(v(19),v(22)))]))],
        [3,100,context(v(13),v(14),v(25))],
        [4,358,context(v(5),v(25),p(v(26),v(27)))],
        [5,353,p(v(26),v(20))],[6,353,p(v(27),v(23))]])
    nil=review.payload()
    join_nil=entry(100,context(v(0),nil,nil),[])
    join_step=entry(100,context(v(0),p(p(v(1),v(2)),v(3)),p(p(v(1),v(4)),v(5))),
                    [[0,28,context(v(2),v(0),seq([v(4)]))],[1,100,context(v(0),v(3),v(5))]])
    row=lambda first:context(v(0),p(p(v(0),v(1)),p(v(2),p(v(3),v(4)))),p(v(1),p(v(2),v(3 if first else 4))))
    lift_nil=context(v(0),nil,nil)
    lift=lambda leaf,rec:entry(rec,context(v(0),p(v(1),v(2)),p(v(3),v(4))),
                              [[0,leaf,context(v(0),v(1),v(3))],[1,rec,context(v(0),v(2),v(4))]])
    return [reader,join_nil,join_step,entry(354,row(True),[]),entry(355,row(False),[]),
            entry(356,lift_nil,[]),lift(354,356),entry(357,lift_nil,[]),lift(355,357),
            entry(358,context(v(0),v(1),p(v(2),v(3))),
                  [[0,356,context(v(0),v(1),v(2))],[1,357,context(v(0),v(1),v(3))]])]


def program(engine,data):
    code='use '+investigate.ml_string(str(engine))+';\n'+review.PRELUDE
    code+=r'''
fun emitPrefixed (i,u,rs) = let
 val result = case N.finite_prefixed_observation_outputs u rs of NONE => "null"
  | SOME (xs,ys) => "[" ^ jlist jterm xs ^ "," ^ jlist jterm ys ^ "]"
 in print ("PREFIX_RESULT " ^ Int.toString i ^ " {\"owner\":" ^ jterm u ^
  ",\"rows\":" ^ jlist jterm rs ^ ",\"outputs\":" ^ result ^ "}\n") end;
val () = emitCompiledLibrary 0 N.inference_claim_construction_library;
val () = emitCompiledLibrary 1 N.inference_reader_investigation_library;
val () = emitCompiledLibrary 2 N.keyed_table_construction_library;
val () = print ("SOURCE_RESULT " ^ "{\"value\":" ^ jterm (N.finite_literal_inference_value []) ^
 ",\"known\":" ^ jlist jcall (N.finite_literal_inference_known []) ^ "}\n");
'''
    rows=[f'({i},{review.ml_term(c["owner"])},{investigate.ml_list(c["rows"],review.ml_term)})'
          for i,c in enumerate(data['cases'])]
    code+='val () = List.app emitPrefixed ['+','.join(rows)+'];\n'
    return code


def assess(data,raw):
    reports,libraries,sources={},{},[]
    for line in raw.splitlines():
        if line.startswith('PREFIX_RESULT '):
            _,i,s=line.split(' ',2);i=int(i);assert i not in reports;reports[i]=json.loads(s)
        elif line.startswith('COMPILED_LIBRARY '):
            _,i,s=line.split(' ',2);i=int(i);assert i not in libraries;libraries[i]=json.loads(s)
        elif line.startswith('SOURCE_RESULT '):sources.append(json.loads(line.split(' ',1)[1]))
    assert set(reports)==set(range(len(data['cases']))) and set(libraries)=={0,1,2} and len(sources)==1
    expected=libraries[1]+tables.expected_library()+expected_new_library()
    assert [review.schema_key(x['schema']) for x in libraries[2]]==[review.schema_key(x['schema']) for x in tables.expected_library()]
    assert [x['entry'] for x in libraries[0]]==[x['entry'] for x in expected]
    mismatches=[{'index':i,'actual':a,'expected':b} for i,(a,b) in enumerate(zip(libraries[0],expected))
                if review.schema_key(a['schema'])!=review.schema_key(b['schema'])]
    assert not mismatches, ('compiled_clause_mismatches',mismatches)
    for item in libraries[0]:
        assert set(map(review.freeze,item['enumeration']))==set(map(review.freeze,item['schema']['premises']))
        assert len(item['enumeration'])==len(item['schema']['premises'])
    checked=[]
    for i,c in enumerate(data['cases']):
        expected={'owner':c['owner'],'rows':c['rows'],'outputs':project(c['owner'],c['rows'])}
        assert reports[i]==expected,(c['name'],reports[i],expected)
        checked.append({'name':c['name'],**reports[i]})
    assert review.formed(sources[0]['value'])
    assert [d for d,t in sources[0]['known']]==[94,294,126,125,61,61,345,346]
    assert all(review.formed(t) for d,t in sources[0]['known'])
    assert sources[0]['known'][4]==sources[0]['known'][5]
    recovery=source_reader.recover_argument(sources[0]['value'],data['source_spec'])
    return {'source_recovery':recovery,'cases':len(checked),'complete_projection_results':checked,'compiled_library':libraries[0],
            'original_inference_library':libraries[1],'source_example':sources[0],
            'boundary':'All complete actual projections and compiled schema fields are checked, including every premise occurrence. Original source operands and all eight proved initial calls are retained. Native construction of entries 350 and 359 from these inputs is a separate required next gate.'}


def main():
    p=argparse.ArgumentParser()
    for name in ['proof','poly','project','output']:p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args()
    receipt=proved_code.checked_execution(a.proof,a.poly,a.output,project=a.project.resolve(),
        required_theories=['Factor_Inference_Claim_Compilation','Factor_Inference_Claim_Contracts','Factor_Prefixed_Observation_Execution'],
        inputs=inputs(),input_paths=[Path(__file__),Path(tables.__file__),Path(tables.table_cases.__file__),SOURCE_SPEC],
        program=program,assess=assess,timeout=120,
        question='Do actual paired projections retain every owner, local key, callee, value and occurrence, and does the compiled reader have the complete stated native premises?',
        boundary='The universal kernel equations and exact compiled-clause contracts govern the emitted operations. The finite family supplements them; source-driven closure and symbolic local-reading correspondence remain explicit requirements.')
    print(json.dumps({'status':receipt['status'],'error':receipt.get('error'),'cases':receipt.get('assessment',{}).get('cases')}))
    return int(receipt['status']!='accepted')


if __name__=='__main__':raise SystemExit(main())
