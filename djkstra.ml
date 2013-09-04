(*
 Program : djikstra's algo
 Author : Arpit Agarwal
 Date : 25/8/13
*)


open Queue
open Array
open List
open HashTable
open ListPair
open Option

exception InvalidInput;
exception NotFound;


(*membership in a list*)
infix mem;
fun x mem [] = false | x mem ((y)::tl) = (x=y) orelse (x mem tl);

(* find outgoing edges from a vertex *)
fun outgoing (v,[]) = [] | outgoing (v:string,(x,y,w)::triplets) = 
if v=x then (x,y,real(w)) :: outgoing(v,triplets)
else
outgoing(v,triplets);

(* make vertex set from a given Graph *)
fun vertexSet([],vertexlist,vq:(string) queue) = vq | vertexSet((x,y,z)::triplets,vertexlist,vq:(string) queue)=
let 
in
if not(x mem (vertexlist)) then
	if not(y mem (vertexlist)) then
	(
        enqueue(vq,x);
        enqueue(vq,y);
        vertexSet(triplets,vertexlist@[(x)]@[(y)],vq)
	)
	else
	(
	enqueue(vq,x);
        vertexSet(triplets,vertexlist@[(x)],vq)
	)
else 
if not(y mem (vertexlist)) then
	(
	enqueue(vq,y);
        vertexSet(triplets,vertexlist@[(y)],vq)
	)
else vertexSet(triplets,vertexlist,vq)
end;

(*Creates a list of pairs with 2nd element of pairs having same value*)
fun createList (n :int) =
let val lt = []
in
if(n=0) then lt
else
if(n=1) then createList(n-1) @ [0.0]
else
createList(n-1) @ [Real.posInf]
end;

(*hash is vertex distance map , distance from source*)
(* increases priority of key in the hash map*)
fun incr_prio (hash,v:string,d_new:real) = 
let
in
HashTable.remove hash (v);
HashTable.insert hash (v,d_new)
end;

(* extracts (key,value) from a hash_map having the minimum value *)
fun  extract_min_hash(hash,(x)::tl,vq:(string) queue,min:real,v:string) =
let
in
case (find hash(x)) of
SOME(d') =>
	 if(d' < min) then
	(
	extract_min_hash(hash,tl,vq,d',x)
	)
	else
	(
	extract_min_hash(hash,tl,vq,min,v)
	)

end
| extract_min_hash(hash,[],vq:(string) queue,min:real,v:string) = 
let in
		HashTable.remove hash (v);
		delete (vq,fn (x) => x=v);
		(v,min) 
end;

(* forms a shortest path from source to destination using a (vertex,parent) map*)
(*parent of a vertex 'v' is the vertex which relaxed the edge from parent to vertex 'v'*)
fun shortest_path(parent,s:string,d:string,sp)=
let
in
case (find parent(d)) of
	SOME(d') =>
	if(d <> s) then 
		(
		enqueue(sp,d);
		shortest_path(parent,s,lookup parent(d),sp)
		)
	else 
	enqueue(sp,s)
        | NONE => (
		if(d=s) then enqueue(sp,d)
		else ()
		)
end;
(*-------------------------------------------------------------------------------------------------------------------------------------*)


(*--------------------------------------------------------------------------------------------------------------------------------------*)


val visited:(string*real) queue = mkQueue ();
val visited_vertex:(string) queue = mkQueue ();
(* creating shortest path queue*)
val sp:(string) queue = mkQueue ();
(* creating vertex set queue*)
val VQ: (string) queue = mkQueue ();
(*creating Hash Map for lookup*)
val hash:(string,real) hash_table = HashTable.mkTable (HashString.hashString, op=) (40, NotFound);
(*creating Hash Map of vertex to its parent for getting shortest path *)
val parent:(string,string) hash_table = HashTable.mkTable (HashString.hashString, op=) (40, NotFound);
(*creating Hash Map of vertex to its shortest path length from source for lookup*)
val spl:(string,real) hash_table = HashTable.mkTable (HashString.hashString, op=) (40, NotFound);

(*clear all queues and hash maps*)
fun clear () =
let
in
  Queue.clear(VQ);
  Queue.clear(visited);
  Queue.clear(visited_vertex);
  Queue.clear(sp);
  HashTable.clear hash;
  HashTable.clear parent;
  HashTable.clear spl
end;
(*--------------------------------------------------------------------------------------------------------------------------------------*)
(* Dijkstra's Algorithm *)
fun djkss(G,s:string,d:string)=
let
  
  val V=[(s)]
  (* creating vertex set list*)
  val VL = V@contents(vertexSet(G,V,VQ))
  (*creating initial distance from source list for corresponding vertex in VL with s.d =0.0 and v.d (v <> s) = Infinity*)
  val DFSL = createList(List.length (VL))

  fun expand(v: string, d: real) =
    let fun handle_edge(e:string*string*real) =
      let val (_, v', w) = e in
        case (find hash (v')) of
          SOME(d') =>
	     if d+w < d'
              then (
		    (* Relaxing the edge , inserting the end vertex into list of visited vertices and increasing its priority in hash*)
		    HashTable.insert parent(v',v);
		    HashTable.insert spl(v',d+w);
		    enqueue(visited, (v', d+w));
		    enqueue(visited_vertex, (v'));
                    incr_prio(hash, v',d+w)
		   )
            else ()
	    | NONE => 
		    if(v' mem (contents(visited_vertex))) then
		    (
			print("Input Graph contains Cycle or same edge is present two times \n");
			()
		    )
		    else ()
      end
    in
      List.app handle_edge (outgoing(v,G))
    end
in
  enqueue(VQ,s);
  ListPair.appEq (HashTable.insert hash) (VL, DFSL);
  enqueue(visited, (s, 0.0));
  enqueue(visited_vertex, s);
  while (not (numItems hash = 0)) do expand(extract_min_hash(hash,contents(VQ),VQ,Real.posInf,hd(contents(VQ))))
end;

(*--------------------------------------------------------TEST CASES----------------------------------------------------------------*)

(* TEST CASE 1 START *)
(*Normal Graph with no cycles and having a  two paths b/w src and dst*)
print("------------------------------TEST CASE 1 ------------------");
val G=[ ("a","b",4),("b","a",5),("b","c",5),("b","d",4), ("d","e",10),("c","k",1),("d","k",4),("y","z",5),("i","j",7)];
val src = "a";
val dst = "k";
djkss(G,src,dst);
shortest_path(parent,src,dst,sp);
List.rev(contents(sp));
if(src mem (contents(sp)))then
(
print("And the length of shotest path from source to destination is : " ^ Real.toString(lookup spl(dst)) ^ "\n");
print("\nThe Shortest path from source to destination is given below : \n");
List.rev(contents(sp))
)
else
(
print("\nThere is no path between given source and destination according to input Graph. \n");
print("\nThe list of visited vertices using dijkstra's algo is given below : \n");
contents(visited_vertex)
);

(* TEST CASE 1 END *)

(* TEST CASE 2 START *)
(*Graph with a cycle and having a path b/w src and dst*)
print("------------------------------TEST CASE 2 ------------------------");
val G=[ ("a","b",5),("b","a",4),("b","d",5), ("d","e",1),("d","k",3),("k","e",4),("y","z",5),("i","j",7),("e","l",2)];
val src = "a";
val dst = "l";
clear();
djkss(G,src,dst);
shortest_path(parent,src,dst,sp);
List.rev(contents(sp));
if(src mem (contents(sp)))then
(
print("And the length of shotest path from source to destination is : " ^ Real.toString(lookup spl(dst)) ^ "\n");
print("\nThe Shortest path from source to destination is given below : \n");
List.rev(contents(sp))
)
else
(
print("\nThere is no path between given source and destination according to input Graph. \n");
print("\nThe list of visited vertices using dijkstra's algo is given below : \n");
contents(visited_vertex)
);

(* TEST CASE 2 END *)
(* TEST CASE 3 START *)
(*Graph having no path b/w src and dst*)
print("------------------------------TEST CASE 3 ------------------------");
val G=[ ("a","b",5),("b","c",4),("b","d",5), ("d","e",10),("c","k",3),("d","k",4),("y","z",5),("i","j",7)];
val src = "a";
val dst = "z";
clear();
djkss(G,src,dst);
shortest_path(parent,src,dst,sp);
List.rev(contents(sp));
if(src mem (contents(sp)))then
(
print("And the length of shotest path from source to destination is : " ^ Real.toString(lookup spl(dst)) ^ "\n");
print("\nThe Shortest path from source to destination is given below : \n");
List.rev(contents(sp))
)
else
(
print("\nThere is no path between given source and destination according to input Graph. \n");
print("\nThe list of visited vertices using dijkstra's algo is given below : \n");
contents(visited_vertex)
)
(* TEST CASE 3 END *)








