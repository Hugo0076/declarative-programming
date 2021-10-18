% Author:   Hugo Lyons Keenan <hlyonskeenan@student.unimelb.edu.au>
% Purpose:  Solve a fill-in puzzle given a layot and wordlist
%
% First, the program processes the puzzle grid given as input. It finds all of
% the vertical and horizontal 'slots' from columns and rows of the puzzle. Slots
% are discarded if they are smaller than the smallest word in the wordlist.
% The wordlist is matched to trimmed list of slots to produce a pairing of all
% unifiable slots with a given word. This list of slots for each word is then
% sorted. First, words are sorted based on the number of slots they could fit
% into (lower first) and the length of the word (longer first). Then, each 
% word's slot list is sorted based on the number of ground terms in each slot
% (higher is better). The program then attempts to unify the first word in the
% list with the first slot in its slot list, proceeding onto the next if it
% fails. After each word is sucessfully unified, the word/slot list iis updated
% and any words with only one slot remaining are unified and a choicepoint is
% left. The process proceeds until there are no words left to place, or 
% unification fails. If unification fails, the program backtracks to the last
% choicepoint and attempts to solve again. The predicate either fails is no 
% solutions exist, or returns a solved puzzle and the original wordlist if a
% solution is found. 

:- ensure_loaded(library(clpfd)).

% Helper predicates, the utility of these is quite transparent

list_pair_num_slots(Polarity, [Word|[Slots]], L-[Word|[Slots]]) :-
    length(Slots, L_pos),
    L is L_pos * Polarity.

list_pair_word_len(Polarity, [Word|[Slots]], L-[Word|[Slots]]) :-
    length(Word, L_pos),
    L is L_pos * Polarity.

list_pair_s(Polarity, Slot, L-Slot) :-
    length(Slot, L_pos),
    L is L_pos * Polarity.

list_pair_w(Polarity, Word, L) :-
    length(Word, L_pos),
    L is L_pos * Polarity.

list_pair_ground(Polarity, Slot, N-Slot) :-
    num_ground(Slot, N_pos),
    N is N_pos * Polarity.

% Returns the number of ground elements in a slot
num_ground([], 0).
num_ground([El|Slot], N_pos) :-
    (ground(El) ->
        num_ground(Slot, N),
        N_pos is N + 1
    ;
        num_ground(Slot, N_pos)
    ).

sort_word_slots_on_ground_num([Word|[Slots0]], [Word|[Slots]]) :-
    sort_slots_on_ground_num(Slots0, Slots).

sort_slots_on_ground_num(Slots0, Slots) :-
    maplist(list_pair_ground(-1), Slots0, GroundList),
    keysort(GroundList, SortedList),
    maplist(remove_prefix, SortedList, Slots).

remove_prefix(_-Ls, Ls).

remove_suffix([Ls|_], Ls).

% Sort the word/slot list on a number of metrics 
sort_word_slot_list(WordSlotList, WordSlotListSorted) :-
    % sort the word-slot list based on potential slot count, ascending
    maplist(list_pair_num_slots(1), WordSlotList, LenList0),
    keysort(LenList0, SortedList0),
    maplist(remove_prefix, SortedList0, WordSlotList0),
    % sort the word-slot list based on word length
    maplist(list_pair_word_len(-1), WordSlotList0, LenList),
    keysort(LenList, SortedList),
    maplist(remove_prefix, SortedList, WordSlotList1),
    % sort the word-slot list based on number of ground terms
    maplist(sort_word_slots_on_ground_num, WordSlotList1, WordSlotListSorted).

% Remove slots with length lower than a specified number 
trim_slot_list([], _, []).
trim_slot_list([Slot|SlotList0], Min, SlotList) :-
    (length(Slot, Len), Len >= Min ->
        trim_slot_list(SlotList0, Min, SlotList1),
        SlotList = [Slot|SlotList1]
    ;
        trim_slot_list(SlotList0, Min, SlotList)
    ).

% Prints the current state of the puzzle
print_puzzle([]) :-
    nl.
print_puzzle([Row|Puzzle]) :-
    print(Row),
    nl,
    print_puzzle(Puzzle).

% The main predicate to be called, as specified.
% Finds a solution if one exists.
% For a more detailed overview, see file level documentation.
puzzle_solution(Puzzle, WordList) :-
    get_slots_from_matrix_master(Puzzle, Slots0),
    maplist(list_pair_w(1), WordList, WordLenOnlyList),
    min_member(Min, WordLenOnlyList),
    trim_slot_list(Slots0, Min, Slots),
    match_words_to_slots(WordList, Slots, WordSlotList),
    sort_word_slot_list(WordSlotList, WordSlotListSorted),
    % attempt to solve the puzzle, terminate after one solution is found
    solve(WordSlotListSorted, Slots, Puzzle), !.

% This is the main workhorse predicate, it is responsible for unifying each word
% with a slot and updating the internal representation.
solve([],_, _).
solve([WordSlot|WordSlotList], Slots, Puzzle) :-
    WordSlot = [Word|[SlotList]],
    member(Slot, SlotList),
    % attempt to unify word with current choice of slot
    Slot = Word,
    % if successful, move on with remaining words/slots
    match_words_to_slots_with_SL(WordSlotList, WordSlotList0),
    sort_word_slot_list(WordSlotList0, WordSlotListSorted),
    solve(WordSlotListSorted, Slots, Puzzle).

% Gets all slots from a matrix
get_slots_from_matrix_master(Puzzle, Slots) :-
    % horizontal slots
    get_slots_from_matrix(Puzzle, HSlots),
    % vertical slots
    transpose(Puzzle, PuzzleT),
    get_slots_from_matrix(PuzzleT, VSlots),
    append(HSlots, VSlots, Slots).

% Given a matrix of variables/atoms, find all the slots that exist in it.
get_slots_from_matrix([Row], Slots) :-
    get_slots_from_vector(Row, Slots).
    
get_slots_from_matrix([Row|Rows], Slots):- 
    get_slots_from_vector(Row, Slots_0),
    append(Slots_0, Slots_1, Slots),
    get_slots_from_matrix(Rows, Slots_1),
    !.

% Given a vector of variables/atoms, find all the slots that exist in it.
get_slots_from_vector([], _).
get_slots_from_vector([El|Row], Slots) :-
    (nonvar(El), El = '#' -> 
        % if we read '#' move to the next index, this is not the start of a slot
        get_slots_from_vector(Row, Slots)
    ;   
        read_slot([El|Row], Slot, Rest),
        % print(Slot),
        get_slots_from_vector(Rest, Slots_Rest),
        append(Slots_Rest, [Slot], Slots)
    ), !. % maybe fix later

% Given a vector of variables/atoms starting at a non '#', find the first slot
% that exists in it, as well as the remaining elements.
read_slot(Row, Slot, Rest) :-
    append(Slot_0, Rest, Row),
    % if we have reached the end of the line, we have a slot: return it
    (length(Rest,0) ->
        % if the last character is a #, remove it
        (   length(Slot_0, Len_0),
            nth1(Len_0, Slot_0,End, Slot_1),
            nonvar(End),
            End = '#'  ->
            Slot = Slot_1
        ;
            Slot = Slot_0
        )
    ;
        length(Slot_0, Len),
        Len > 0,
        nth1(Len, Slot_0, End, Slot),
        nonvar(End),
        End = '#'
    ).

% Given a list of words and slots, match words to slots they could fit in,
% return this result as a list.
match_words_to_slots([], _, []).
match_words_to_slots([Word|Words], Slots, WordsSlotList) :-
    match_word_to_slots(Word, Slots, SlotList_0),
    Entry = [Word,SlotList_0], 
    WordsSlotList = [Entry|WordSlotList_0],
    match_words_to_slots(Words, Slots, WordSlotList_0).

% This is the same as the function above, but it only uses the slot list
% associated with each word, reducing the search cost.
match_words_to_slots_with_SL([], []).
match_words_to_slots_with_SL([WordSlot|WordSlots], WordsSlotList) :-
    WordSlot = [Word|[Slots]],
    match_word_to_slots(Word, Slots, SlotList_0),
    % check if after removing slot, other words have only one remaining option,
    % unify if so
    (length(SlotList_0, Len), Len = 1 ->
        % length = 1, try to unify 
        [Slot] = SlotList_0,
        Slot = Word,
        WordsSlotList = WordSlotList_0
    ;
        Entry = [Word,SlotList_0], 
        WordsSlotList = [Entry|WordSlotList_0]
    ),
    match_words_to_slots_with_SL(WordSlots, WordSlotList_0).

% Given a word and a list of slots, find the slots the word could fit in,
% return this as a list
match_word_to_slots(_, [], []).
match_word_to_slots(Word, [Slot|Slots], SlotList) :-
    % Check if Slot unifies with Word, add to list if so, recurse
    (unifiable(Word, Slot, _) ->
        SlotList = [Slot|SlotList_0],
        match_word_to_slots(Word, Slots, SlotList_0)
    ;
        match_word_to_slots(Word, Slots, SlotList)
    ).