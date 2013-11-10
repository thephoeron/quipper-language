# This file is part of Quipper. Copyright (C) 2011-2013. Please see the
# file COPYRIGHT for a list of authors, copyright holders, licensing,
# and other details. All rights reserved.
# 
# ======================================================================

BEGIN{
    LOOK_FOR_ENTRY="LOOK FOR ENTRY";
    LOOK_FOR_NAME="LOOK FOR NAME";
    LOOK_FOR_END="LOOK FOR END";
    LINE_NBER=0
    
    hasfoundentry = 0
    
    state=LOOK_FOR_ENTRY;
    print_log( "-- state is " state);
}

//{++LINE_NBER;}

/^[^ \t]/{
    print_log( "-- found non-empty line");
    if ( state == LOOK_FOR_NAME ) {
        print_log( "-- state is " state);
        state = LOOK_FOR_END;
        print_log( "-- state changed to LOOK_FOR_END");
        name_def = $0;
        sub(/ .*/,"",name_def);
        print_log( "-- name_def = " name_def);
    }
    else if ( state == LOOK_FOR_END ){
        print_log( "-- state is " state);
        first_word = $0;
        sub(/ .*/,"", first_word);
        print_log( "-- first word is " first_word);
        if (first_word != name_def) {
            print_log( "-- first word is not name_def");
            print_log( "-- v1 : normal")
            print text_build_circuit;
            print_log( "-- v2 : lifted")
            gsub(/\n/, "\n                      ", text_build_circuit);
            gsub(/--[^\n]*/, "", text_build_circuit); # filter comments out
            # The following line is somehow necessary for haddock of
            # ghc 7.4.2 to correctly match documentations with
            # declarations.
            print "{-# LINE " (LINE_NBER-1) " " haskell_filename " #-}";
            print        "$( decToCircMonad [d| " text_build_circuit;
            print " |] ) ";    
            print "{-# LINE " LINE_NBER " " haskell_filename " #-}";
            state = LOOK_FOR_ENTRY;
        }
    }
}

($0 !~ /^build_circuit/){ 
    if ( state == LOOK_FOR_ENTRY ) {
        print;
    } else if (state == LOOK_FOR_END) {
        print_log( "-- storing line : " $0)
        text_build_circuit = text_build_circuit $0 "\n";
    }
}

/^build_circuit/{
    print_log( "-- found a build_circuit");
    if ( state == LOOK_FOR_ENTRY) {
        print_log( "-- state is " state)
        state = LOOK_FOR_NAME;
        print_log( "-- state changed to LOOK_FOR_NAME")
        text_build_circuit = "";
        if ($0 ~ /[ \t][^ \t]/) { # the definition starts right after
            print_log( "-- found a name on the same line as build_circuit!")
            text_build_circuit = $0
            sub(/[^ \t]*[ \t]*/,"",text_build_circuit);
            text_build_circuit = text_build_circuit "\n";
            name_def = text_build_circuit;
            sub(/ .*/,"",name_def);
            print_log( "-- name_def = " name_def);
            state = LOOK_FOR_END
        } else {
            # pad a newline for the removed build_circuit.
            print ""
        }
    } else {
        print_log( "-- state is " state " : inconsistent state?")
        print_log( "-- change to LOOK_FOR_NAME anyway")
        state = LOOK_FOR_NAME;
        print_log( "-- state changed to LOOK_FOR_NAME")
        text_build_circuit = "";
    }
}





END{
    if (state == LOOK_FOR_END){
        print_log( "-- state is " state);
        first_word = $0;
        sub(/ .*/,"", first_word);
        print_log( "-- first word is " first_word);
#        if (first_word != name_def) {
#            print_log( "-- first word is not name_def")
            print_log( "-- v1 : normal")
            print text_build_circuit;
            gsub(/--[^\n]*/, "", text_build_circuit); # filter comments out
            print_log( "-- v2 : lifted")
            gsub(/\n/, "\n                      ", text_build_circuit);
            print        "$( decToCircMonad [d| " text_build_circuit;
            print " |] ) ";
            state = LOOK_FOR_ENTRY;
#        }
    }
}

# if n = 0, do not log. If n = 1, do log.
function print_log(s) {
    if ( LOG_LEVEL == 1 ) { print s; }
}

