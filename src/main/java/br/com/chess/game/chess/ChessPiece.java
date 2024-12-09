package br.com.chess.game.chess;


import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.Piece;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.exceptions.ChessException;
import br.com.chess.game.chess.utils.Color;


public abstract class ChessPiece extends Piece {

    //@ spec_public
    private final Color color;

    //@ spec_public
    private int moveCount;


    /*@ public normal_behavior
      @     requires color != null;
      @     ensures this.color == color;
      @ pure
      @*/
    public ChessPiece(Board board, Color color) {
        super(board);
        this.color = color;
        this.moveCount = 0;
    }

    /*@ public normal_behavior
      @     ensures \result == color;
      @ pure
      @*/
    public Color getColor() {
        return color;
    }

    /*@ public normal_behavior
      @     ensures \result == moveCount;
      @ pure
      @*/
    public int getMoveCount() {
        return moveCount;
    }

    /*@ public normal_behavior
      @     requires moveCount < Integer.MAX_VALUE;
      @     ensures moveCount == \old(moveCount) + 1;
      @ assigns moveCount;
      @*/
    public void increaseMoveCount(){
        moveCount++;
    }

    /*@ public normal_behavior
      @     requires moveCount > Integer.MIN_VALUE;
      @     ensures moveCount == \old(moveCount) - 1;
      @ assigns moveCount;
      @*/
    public void decreaseMoveCount(){
        moveCount--;
    }


    /*@ public normal_behavior
      @     requires getBoard().positionExists(position);
      @     requires getBoard().pieces[position.getRow()][position.getColumn()] == null;
      @     ensures \result == false;
      @ also
      @ public normal_behavior
      @     requires getBoard().positionExists(position);
      @     requires getBoard().pieces[position.getRow()][position.getColumn()] != null;
      @     requires \typeof(getBoard().pieces[position.getRow()][position.getColumn()]) <: \type(ChessPiece);
      @     ensures \result == (((ChessPiece) getBoard().pieces[position.getRow()][position.getColumn()]).getColor() != getColor());
      @ pure
      @*/
    public boolean isThereOpponentPiece(Position position) {
        /*@ nullable*/ Piece piece = getBoard().piece(position);
        if (piece == null) {
            return false;
        }

        ChessPiece p = (ChessPiece) piece;
        return p.getColor() != getColor();
    }

    /*@ public normal_behavior
      @     requires position != null;
      @     requires position.getRow() >= 0 && position.getRow() <= 7;
      @     requires position.getColumn() >= 0 && position.getColumn() <= 7;
      @     requires position.getColumn() <= Character.MAX_VALUE - 'a';
      @     requires 8 - position.getRow() <= Integer.MAX_VALUE;
      @     ensures \result != null;
      @     ensures \result.getRow() == 8 - position.getRow();
      @     ensures \result.getColumn() == (char) ('a' + position.getColumn());
      @     assignable \nothing;
      @ also
      @ public normal_behavior
      @     requires position == null;
      @     ensures \result == null;
      @     assignable \nothing;
      @ also
      @ public exceptional_behavior
      @     requires position != null;
      @     requires position.getRow() < 0 || position.getRow() > 7 || position.getColumn() < 0 || position.getColumn() > 7;
      @     requires position.getColumn() <= Character.MAX_VALUE - 'a';
      @     requires 'a' + position.getColumn() >= 0;
      @     requires 8 - position.getRow() <= Integer.MAX_VALUE;
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public /*@ nullable*/ ChessPosition getChessPosition(){
        return ChessPosition.fromPosition(position);
    }
}

