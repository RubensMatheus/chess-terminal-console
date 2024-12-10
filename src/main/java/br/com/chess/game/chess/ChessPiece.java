package br.com.chess.game.chess;


import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.Piece;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.exceptions.ChessException;
import br.com.chess.game.chess.utils.Color;


public abstract class ChessPiece extends Piece {

    private final Color color; //@ in modelColor;
    private int moveCount; //@ in modelCount;

    //@ public model Color modelColor;
    //@ private represents modelColor = this.color;

    //@ public model int modelCount;
    //@ private represents modelCount = this.moveCount;

    /*@ public normal_behavior
      @     requires color != null;
      @     ensures modelColor == color;
      @ pure
      @*/
    public ChessPiece(Board board, Color color) {
        super(board);
        this.color = color;
        this.moveCount = 0;
    }

    /*@ public normal_behavior
      @     ensures \result == modelColor;
      @ pure
      @*/
    public Color getColor() {
        return color;
    }

    /*@ public normal_behavior
      @     ensures \result == modelCount;
      @ pure
      @*/
    public int getMoveCount() {
        return moveCount;
    }

    /*@ public normal_behavior
      @     requires modelCount < Integer.MAX_VALUE;
      @     ensures modelCount == \old(modelCount) + 1;
      @ assigns modelCount;
      @*/
    public void increaseMoveCount(){
        moveCount++;
    }

    /*@ public normal_behavior
      @     requires modelCount > Integer.MIN_VALUE;
      @     ensures modelCount == \old(modelCount) - 1;
      @ assigns modelCount;
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
      @     requires modelPosition != null;
      @     requires modelPosition.getRow() >= 0 && modelPosition.getRow() <= 7;
      @     requires modelPosition.getColumn() >= 0 && modelPosition.getColumn() <= 7;
      @     requires modelPosition.getColumn() <= Character.MAX_VALUE - 'a';
      @     requires 8 - modelPosition.getRow() <= Integer.MAX_VALUE;
      @     ensures \result != null;
      @     ensures \result.getRow() == 8 - modelPosition.getRow();
      @     ensures \result.getColumn() == (char) ('a' + modelPosition.getColumn());
      @     assignable \nothing;
      @ also
      @ public normal_behavior
      @     requires modelPosition == null;
      @     ensures \result == null;
      @     assignable \nothing;
      @ also
      @ public exceptional_behavior
      @     requires modelPosition != null;
      @     requires modelPosition.getRow() < 0 || modelPosition.getRow() > 7 || modelPosition.getColumn() < 0 || modelPosition.getColumn() > 7;
      @     requires modelPosition.getColumn() <= Character.MAX_VALUE - 'a';
      @     requires 'a' + modelPosition.getColumn() >= 0;
      @     requires 8 - modelPosition.getRow() <= Integer.MAX_VALUE;
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public /*@ nullable*/ ChessPosition getChessPosition(){
        return ChessPosition.fromPosition(position);
    }
}

