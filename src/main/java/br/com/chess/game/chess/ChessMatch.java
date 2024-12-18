package br.com.chess.game.chess;

import br.com.chess.game.boardgame.*;
import br.com.chess.game.boardgame.exceptions.BoardException;
import br.com.chess.game.chess.exceptions.ChessException;
import br.com.chess.game.chess.utils.Color;
import br.com.chess.game.pieces.*;

import java.security.InvalidParameterException;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
public class ChessMatch {
    //@ spec_public
    private /*@ nullable*/ ChessPiece enPassantVulnerable;
    //@ spec_public
    private /*@ nullable*/ ChessPiece promoted;
    //@ spec_public
    private Board board;
    //@ spec_public
    private Integer turn;
    //@ spec_public
    private Color currentPlayer;
    //@ spec_public
    private boolean check;
    //@ spec_public
    private boolean checkMate;

    //@ spec_public
    private List<ChessPiece> piecesOnTheBoard;
    //@ spec_public
    private List<ChessPiece> capturedChessPieces;

    //@ public invariant piecesOnTheBoard.size() >= 0;
    //@ public invariant capturedChessPieces.size() >= 0;

    /*@ public normal_behavior
      @     ensures \result == this.turn;
      @ pure
      @*/
    public Integer getTurn() {
        return turn;
    }

    /*@ public normal_behavior
      @     ensures \result == this.currentPlayer;
      @ pure
      @*/
    public Color getCurrentPlayer() {
        return currentPlayer;
    }

    /*@ public normal_behavior
      @     ensures \result == this.check;
      @ pure
      @*/
    public boolean isCheck() {
        return check;
    }

    /*@ public normal_behavior
      @     ensures \result == this.checkMate;
      @ pure
      @*/
    public boolean isCheckMate() {
        return checkMate;
    }

    /*@ public normal_behavior
      @     ensures \result == this.enPassantVulnerable;
      @ pure
      @*/
    public /*@ nullable*/ ChessPiece getEnPassantVulnerable() {
        return enPassantVulnerable;
    }

    /*@ public normal_behavior
      @     ensures \result == this.promoted;
      @ pure
      @*/
    public /*@ nullable*/ ChessPiece getPromoted() {
        return promoted;
    }

    /*@ public normal_behavior
      @     ensures \result == this.board;
      @ pure
      @*/
    public Board getBoard() {
        return board;
    }

    /*@ ensures board.rows == 8 && board.columns == 8;
      @ ensures turn == 1;
      @ ensures currentPlayer == Color.WHITE;
      @ ensures !check && !checkMate;
      @ ensures piecesOnTheBoard != null && capturedChessPieces != null;
      @ ensures piecesOnTheBoard.size() > 0;
      @ ensures board.pieces.length == board.rows;
      @ ensures (\forall int x; 0 <= x && x < board.rows; board.pieces[x].length == board.columns);
      @ ensures (\forall int x; 0 <= x && x < board.rows;
      @         (\elemtype(\typeof(board.pieces[x])) == \type(ChessPiece)));
      @*/
    public ChessMatch() {
        board = new Board();
        //@ assert board.rows > 0 && board.columns > 0;
        turn = 1;
        currentPlayer = Color.WHITE;
        check = false;
        checkMate = false;
        piecesOnTheBoard = new ArrayList<>();
        capturedChessPieces = new ArrayList<>();
        initialSetup();
        //@ assert board.rows > 0 && board.columns > 0;

    }


    //@ ensures \result.length == 8;
    //@ ensures (\forall int x; 0 <= x && x < \result.length; \result[x].length == 8);
    //@ pure
    public /*@ nullable*/ ChessPiece[][] getChessPieces() {
        return board.getPieces();
    }

    /*@ ensures board.pieces.length == board.rows;
      @ ensures (\forall int i; 0 <= i && i < board.rows; board.pieces[i].length == board.columns);
      @ ensures (\forall int i; 0 <= i && i < board.rows; (\elemtype(\typeof(board.pieces[i])) == \type(ChessPiece)));
      @*/
    public /*@ nullable*/ ChessPiece performChessMove(ChessPosition sourcePosition, ChessPosition targetPosition) {
        Position source = sourcePosition.toPosition();
        Position target = targetPosition.toPosition();
        validateSourcePosition(source);
        validateTargetPosition(source, target);

       /*@ nullable*/ ChessPiece capturedChessPiece = makeMove(source, target);
        if (testCheck(currentPlayer)) {
            undoMove(source, target, capturedChessPiece);
            throw new ChessException("Você não pode se colocar em check");
        }

        /*@ nullable */ ChessPiece movedChessPiece = board.piece(target);

        //#specialmove promotion
        promoted = null;
        if(movedChessPiece instanceof Pawn){
            if((movedChessPiece.getColor() == Color.WHITE && target.getRow() == 0 )||(movedChessPiece.getColor() == Color.BLACK && target.getRow() == 7 )){
                promoted =  board.piece(target);
                promoted = replacepromotedChessPiece("A");
            }
        }

        Color opponent = opponent(currentPlayer);

        check = testCheck(opponent);
        if (testCheckMate(opponent(currentPlayer))) {
            checkMate = true;
        } else {
            //@ assume turn < Integer.MAX_VALUE;
            nextTurn();
        }


        // #specialmove en passant
        if (movedChessPiece instanceof Pawn) {
            if(board.positionExists(source) && (target.getRow() == (source.getRow() - 2) || target.getRow() == (source.getRow() + 2)))
                enPassantVulnerable = movedChessPiece;
        }
        else {
            enPassantVulnerable = null;
        }

       return capturedChessPiece;
    }


    //@ ensures  board.pieces.length == board.rows;
    //@ ensures (\forall int x; 0 <= x && x < board.rows; board.pieces[x].length == board.columns);
    //@ ensures (\forall int x; 0 <= x && x < board.rows; (\elemtype(\typeof(board.pieces[x])) == \type(ChessPiece)));
    public ChessPiece replacepromotedChessPiece(String type){
        if(promoted == null){
            throw new IllegalStateException("Não há peça para ser promovida");
        }
        if(!type.equals("T") && !type.equals("A") && !type.equals("C") && !type.equals("B")){
            throw new InvalidParameterException("Tipo invalido de promoção");
        }

        //@assert type.equals("T") || type.equals("A") || type.equals("C") || type.equals("B");

        /*@ nullable*/ ChessPosition chessPosition = promoted.getChessPosition();

        if(chessPosition == null || !board.thereIsAPiece(chessPosition.toPosition())){
            throw new InvalidParameterException("Não há peça para ser promovida");
        }

        Position position = chessPosition.toPosition();

        //@ assert position.row < board.getRows();
        //@ assert position.column < board.getColumns();
        //@ assert board.pieces[position.row][position.column] != null;
        ChessPiece p = board.removeChessPiece(position);
        piecesOnTheBoard.remove(p);
        ChessPiece newChessPiece = newChessPiece(type, promoted.getColor());
        board.placeChessPiece(newChessPiece,position);
        piecesOnTheBoard.add(newChessPiece);

        return newChessPiece;
    }

    /*@ requires type.equals("B") || type.equals("C") || type.equals("A") || type.equals("T");
      @ ensures (\result instanceof Bishop) <==> type.equals("B");
      @ ensures (\result instanceof Knight) <==> type.equals("C");
      @ ensures (\result instanceof Queen) <==> type.equals("A");
      @ ensures (\result instanceof Rook) <==> type.equals("T");
      @ ensures \result.getColor() == color;
      @ ensures \result.getBoard() == board;
      @ pure
      @*/
    private ChessPiece newChessPiece(String type, Color color) {
        if (type.equals("B")) return new Bishop(board, color);
        if (type.equals("C")) return new Knight(board, color);
        if (type.equals("A")) return new Queen(board, color);
        return new Rook(board, color);
    }


    /*@ assignable \nothing;
      @ ensures board.positionExists(position);
      @ ensures board.pieces[position.row][position.column] != null;
      @ helper
      @*/
    private void validateSourcePosition(Position position) {
        if (!board.thereIsAPiece(position)) {
            throw new ChessException("Não há nenhuma peça na posição de origem.");
        }
        //@ assert board.positionExists(position);
        //@ assert board.pieces[position.row][position.column] != null;

        ChessPiece piece = board.piece(position);
        //@ assert piece != null;

        if (currentPlayer != piece.getColor()) {
            throw new ChessException("A peça escolhida não é sua.");
        }

        if (!piece.isThereAnyPossibleMove()) {
            throw new ChessException("Não há movimentos possíveis para a peça escolhida");
        }

    }

    //@ ensures \result.length == 8;
    //@ ensures (\forall int i; 0 <= i && i < \result.length;
    //@             \result[i].length == 8);
    //@ assignable \nothing;
    public boolean[][] possibleMoves(ChessPosition sourcePosition) {
        Position position = sourcePosition.toPosition();
        validateSourcePosition(position);
        ChessPiece piece = board.piece(position);
        return piece.possibleMoves();
    }


    /*@ ensures board.pieces.length == board.rows;
      @ ensures (\forall int i; 0 <= i && i < board.rows; board.pieces[i].length == board.columns);
      @ ensures (\forall int i; 0 <= i && i < board.rows;
      @     (\elemtype(\typeof(board.pieces[i])) == \type(ChessPiece)));
      @*/
    private /*@ nullable*/ ChessPiece makeMove(Position source, Position target) {

        /*@ nullable*/ ChessPiece p = board.removeChessPiece(source);

        if (p == null) {
            throw new ChessException("Não há nenhuma peça na posição de origem.");
        }
        //@ assume p.modelCount < Integer.MAX_VALUE;
        p.increaseMoveCount();
        /*@ nullable*/ ChessPiece capturedChessPiece = board.removeChessPiece(target);
        board.placeChessPiece(p, target);

        if (capturedChessPiece != null) {
            piecesOnTheBoard.remove(capturedChessPiece);
            capturedChessPieces.add(capturedChessPiece);
        }

        //#Special move castling king side rook
        if(p instanceof King && target.getColumn() == (source.getColumn() + 2)){
            Position sourceT = new Position(source.getRow(), source.getColumn() + 3);
            Position targetT = new Position(source.getRow(), source.getColumn() + 1);

            //@ assert sourceT.column > targetT.column;
            //@ assert sourceT.row == sourceT.row;
            //@ assert sourceT.column < board.columns ==> targetT.column < board.columns;
            /*@ nullable*/ ChessPiece rook = board.removeChessPiece(sourceT);
            if(rook != null) {
                board.placeChessPiece(rook,targetT);
                //@ assume rook.modelCount < Integer.MAX_VALUE;
                rook.increaseMoveCount();
            }

        }
        //#Special move castling king side rook
        else if(p instanceof King && target.getColumn() == source.getColumn() - 2){
            Position sourceT = new Position(source.getRow(), source.getColumn() - 4);
            Position targetT = new Position(source.getRow(), source.getColumn() - 1);
            //@ assert sourceT.column < targetT.column;
            //@ assert sourceT.row == sourceT.row;
            //@ assert sourceT.column >= 0 ==> targetT.column >=0;
                /*@ nullable*/ ChessPiece rook =  board.removeChessPiece(sourceT);
                if(rook != null) {
                    board.placeChessPiece(rook, targetT);
                    //@ assume rook.modelCount < Integer.MAX_VALUE;
                    rook.increaseMoveCount();
                }
        }
        // #specialmove en passant
        if (p instanceof Pawn) {
            if (source.getColumn() != target.getColumn() && capturedChessPiece == null) {
                Position pawnPosition;
                if (p.getColor() == Color.WHITE) {
                    pawnPosition = new Position(target.getRow() + 1, target.getColumn());
                }
                else {
                    pawnPosition = new Position(target.getRow() - 1, target.getColumn());
                }
                    capturedChessPiece = board.removeChessPiece(pawnPosition);
                    if(capturedChessPiece != null) {
                        capturedChessPieces.add(capturedChessPiece);
                        piecesOnTheBoard.remove(capturedChessPiece);
                    }
            }
        }

        return capturedChessPiece;
    }

    /*@ ensures board.pieces.length == board.rows;
      @ ensures (\forall int i; 0 <= i && i < board.rows; board.pieces[i].length == board.columns);
      @ ensures (\forall int i; 0 <= i && i < board.rows; (\elemtype(\typeof(board.pieces[i])) == \type(ChessPiece)));
      @*/
    private void undoMove(Position source, Position target, /*@ nullable*/ ChessPiece captured) {
        /*@ nullable*/ ChessPiece p = board.removeChessPiece(target);

        if(p == null) {
            throw new ChessException("Não há nenhuma peça na posição de destino.");
        }
        //@ assume p.modelCount > Integer.MIN_VALUE;
        p.decreaseMoveCount();
        board.placeChessPiece(p, source);

        if (captured != null) {
            board.placeChessPiece(captured, target);
            capturedChessPieces.remove(captured);
            piecesOnTheBoard.add(captured);
        }
        //#Special move castling king side rook
        if(p instanceof King && target.getColumn() == source.getColumn() + 2){
            Position sourceT = new Position(source.getRow(), source.getColumn() + 3);
            Position targetT = new Position(source.getRow(), source.getColumn() + 1);
            //@ assert sourceT.column > targetT.column;
            //@ assert sourceT.row == sourceT.row;
            //@ assert sourceT.column < board.columns ==> targetT.column < board.columns;
                /*@ nullable*/ ChessPiece rook = board.removeChessPiece(targetT);
                if(rook != null) {
                    board.placeChessPiece(rook,sourceT);
                    //@ assume rook.modelCount > Integer.MIN_VALUE;
                    rook.decreaseMoveCount();
                }
        }
        //#Special move castling king side rook
        else if(p instanceof King && target.getColumn() == source.getColumn() - 2){
            Position sourceT = new Position(source.getRow(), source.getColumn() - 4);
            Position targetT = new Position(source.getRow(), source.getColumn() - 1);
            //@ assert sourceT.column < targetT.column;
            //@ assert sourceT.row == sourceT.row;
            //@ assert sourceT.column >= 0 ==> targetT.column >=0;
                /*@ nullable*/ ChessPiece rook = board.removeChessPiece(targetT);
                if(rook != null) {
                    board.placeChessPiece(rook,sourceT);
                    //@ assume rook.modelCount > Integer.MIN_VALUE;
                    rook.decreaseMoveCount();
                }
        }

        // #specialmove en passant
        if (p instanceof Pawn) {
            if (source.getColumn() != target.getColumn() && captured == enPassantVulnerable) {
                /*@ nullable*/ ChessPiece pawn = board.removeChessPiece(target);
                Position pawnPosition;
                if (p.getColor() == Color.WHITE) {
                    pawnPosition = new Position(3, target.getColumn());
                    //@ assert pawnPosition.row < board.rows && pawnPosition.column < board.columns;
                }
                else {
                    pawnPosition = new Position(4, target.getColumn());
                    //@ assert pawnPosition.row < board.rows && pawnPosition.column < board.columns;
                }
                if(pawn != null) {
                    board.placeChessPiece(pawn, pawnPosition);
                }
            }
        }
    }


    //@ requires board.positionExists(source);
    //@ requires board.pieces[source.row][source.column] != null;
    //@ assignable \nothing;
    private void validateTargetPosition(Position source, Position target) {

        ChessPiece sourcePiece = board.piece(source);

        if(sourcePiece.getPosition() == null) {
            throw new ChessException("Peça de origem inválida");
        }

        if (!sourcePiece.possibleMove(target)) {
            throw new ChessException("A peça escolhida não pode se mover para a posição escolhida");
        }
    }

    /*@ requires turn < Integer.MAX_VALUE;
      @ ensures turn == \old(turn) + 1;
      @ assignable turn, currentPlayer;
      @*/
    private void nextTurn() {
        turn++;
        currentPlayer = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
    }

    /*@ requires column >= 'a' && column <= 'h';
      @ requires row >= 1 && row <= 8;
      @ requires board.rows == 8 && board.columns == 8;
      @ ensures board.pieces[8 - row][column - 'a'] == piece;
      @ ensures piecesOnTheBoard.contains(piece);
      @ ensures  board.pieces.length == board.rows;
      @ ensures (\forall int x; 0 <= x && x < board.rows;
      @             board.pieces[x].length == board.columns);
      @ ensures (\forall int x; 0 <= x && x < board.rows;
      @             (\elemtype(\typeof(board.pieces[x])) == \type(ChessPiece)));
      @ ensures turn == \old(turn);
      @ ensures currentPlayer == \old(currentPlayer);
      @ ensures check == \old(check);
      @ ensures board.rows == \old(board.rows);
      @ ensures board.columns == \old(board.columns);
      @ ensures checkMate == \old(checkMate);
      @ ensures capturedChessPieces == \old(capturedChessPieces);
      @*/
    private void placeNewChessPiece(char column, int row, ChessPiece piece) {
        ChessPosition chessPosition = new ChessPosition(column, row);
        Position position = chessPosition.toPosition();
        //@ assert position.getRow() >= 0 && position.getRow() < board.getRows();
        //@ assert position.getColumn() >= 0 && position.getColumn() < board.getColumns();
        board.placeChessPiece(piece, position);
        //@ assert piece.modelPosition != null;
        piecesOnTheBoard.add(piece);
    }



    /*@ ensures (\result == Color.BLACK && color == Color.WHITE) || (\result == Color.WHITE && color == Color.BLACK);
      @ pure
      @*/
    private Color opponent(Color color) {
        return (color == Color.WHITE) ? Color.BLACK : Color.WHITE;
    }

    /*@     requires (\exists ChessPiece p; piecesOnTheBoard.contains(p); p instanceof King && p.getColor() == color);
      @     assignable \nothing;
      @ also
      @     requires !(\exists ChessPiece p; piecesOnTheBoard.contains(p); p instanceof King && p.getColor() == color);
      @     signals_only IllegalStateException;
      @     assignable \nothing;
      @*/
    private ChessPiece king(Color color) {
        List<ChessPiece> list = listColorChessPieces(color);
        for (ChessPiece p : list) {
            if (p instanceof King) {
                return p;
            }
        }
        throw new IllegalStateException("Não existe um rei com a cor " + color);
    }

    /*@ private normal_behavior
      @ pure
      @*/
    private List<ChessPiece> listColorChessPieces(Color color) {
        List<ChessPiece> result = new ArrayList<>();

            /*@ loop_invariant 0 <= i && i <= piecesOnTheBoard.size();
              @ decreasing piecesOnTheBoard.size() - i;
              @*/
            for (int i = 0; i < piecesOnTheBoard.size(); i++) {
                ChessPiece piece = piecesOnTheBoard.get(i);
                if (piece.getColor() == color) {
                    result.add(piece);
                }
            }
        return result;
    }


    //@ pure
    private boolean testCheck(Color color) {
        ChessPiece king = king(color);

        /*@ nullable*/ ChessPosition ckingPosition = king.getChessPosition();

        if(ckingPosition == null) {
            return false;
        }

        Position kingPosition = ckingPosition.toPosition();

        List<ChessPiece> opponentChessPieces = listColorChessPieces(opponent(color));

        for (ChessPiece p : opponentChessPieces) {

            boolean[][] mat = p.possibleMoves();
            //@ assert p.getBoard().rows == 8 && p.getBoard().columns == 8;
            if (mat[kingPosition.getRow()][kingPosition.getColumn()]) {
                return true;
            }
        }
        return false;
    }

    //@ ensures  board.pieces.length == board.rows;
    //@ ensures (\forall int x; 0 <= x && x < board.rows; board.pieces[x].length == board.columns);
    //@ ensures (\forall int x; 0 <= x && x < board.rows; (\elemtype(\typeof(board.pieces[x])) == \type(ChessPiece)));
    //@ ensures (\forall int x; 0 <= x && x < board.rows; (\elemtype(\typeof(board.pieces[x])) == \type(ChessPiece)));
    private boolean testCheckMate(Color color) {
        if (!testCheck(color)) {
            return false;
        }
        List<ChessPiece> list = listColorChessPieces(color);
        for (ChessPiece p : list) {
            boolean[][] mat = p.possibleMoves();
            /*@ maintaining 0 <= i && i <= mat.length;
              @ decreasing mat.length - i;
              @*/
            for (int i = 0; i < mat.length; i++) {
                /*@ maintaining 0 <= j && j <= mat[i].length;
                  @ decreasing mat[i].length - j;
                  @*/

                for (int j = 0; j < mat[i].length; j++) {
                    if (mat[i][j]) {

                        /*@ nullable*/ ChessPosition chessPosition = p.getChessPosition();
                        if(chessPosition != null) {
                            Position source = chessPosition.toPosition();
                            Position target = new Position(i, j);
                            /*@ nullable*/ ChessPiece capturedChessPiece = makeMove(source, target);

                            boolean testCheck = testCheck(color);
                            undoMove(source, target, capturedChessPiece);
                            if (!testCheck) {
                                return false;
                            }
                        }
                    }

                }
            }
        }
        return true;

    }


    /*@ requires board != null;
      @ requires board.rows == 8 && board.columns == 8;
      @ ensures board.pieces != null && board.pieces.length == board.rows;
      @ ensures (\forall int i; 0 <= i && i < board.rows;
      @     board.pieces[i] != null && board.pieces[i].length == board.columns &&
      @     (\elemtype(\typeof(board.pieces[i])) == \type(ChessPiece)));
      @ ensures turn == \old(turn);
      @ ensures currentPlayer == \old(currentPlayer);
      @ ensures check == \old(check);
      @ ensures board.rows == \old(board.rows);
      @ ensures board.columns == \old(board.columns);
      @ ensures checkMate == \old(checkMate);
      @ ensures capturedChessPieces == \old(capturedChessPieces);
      @ ensures piecesOnTheBoard.size() > 0;
      @*/
    private void initialSetup() {
        placeNewChessPiece('a', 1, new Rook(board, Color.WHITE));
        placeNewChessPiece('b', 1, new Knight(board, Color.WHITE));
        placeNewChessPiece('c', 1, new Bishop(board, Color.WHITE));
        placeNewChessPiece('d', 1, new Queen(board, Color.WHITE));
        placeNewChessPiece('e', 1, new King(board, Color.WHITE, this));
        placeNewChessPiece('f', 1, new Bishop(board, Color.WHITE));
        placeNewChessPiece('g', 1, new Knight(board, Color.WHITE));
        placeNewChessPiece('h', 1, new Rook(board, Color.WHITE));
        placeNewChessPiece('a', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('b', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('c', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('d', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('e', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('f', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('g', 2, new Pawn(board, Color.WHITE,this));
        placeNewChessPiece('h', 2, new Pawn(board, Color.WHITE,this));

        placeNewChessPiece('a', 8, new Rook(board, Color.BLACK));
        placeNewChessPiece('b', 8, new Knight(board, Color.BLACK));
        placeNewChessPiece('c', 8, new Bishop(board, Color.BLACK));
        placeNewChessPiece('d', 8, new Queen(board, Color.BLACK));
        placeNewChessPiece('e', 8, new King(board, Color.BLACK, this));
        placeNewChessPiece('f', 8, new Bishop(board, Color.BLACK));
        placeNewChessPiece('g', 8, new Knight(board, Color.BLACK));
        placeNewChessPiece('h', 8, new Rook(board, Color.BLACK));
        placeNewChessPiece('a', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('b', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('c', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('d', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('e', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('f', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('g', 7, new Pawn(board, Color.BLACK,this));
        placeNewChessPiece('h', 7, new Pawn(board, Color.BLACK,this));

    }


}
