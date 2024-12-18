package br.com.chess.game.boardgame;

import br.com.chess.game.boardgame.exceptions.BoardException;
import br.com.chess.game.boardgame.ChessPiece;

public class Board {

    //@ spec_public
    private final int rows;
    //@ spec_public
    private final int columns;
    //@ spec_public
    private /*@ nullable */ ChessPiece[][] pieces;

    //@ public invariant pieces != null;
    //@ public invariant rows  == 8 && columns == 8;
    //@ public invariant pieces.length == rows;
    //@ public invariant (\forall int i; 0 <= i && i < rows; pieces[i] != null);
    //@ public invariant (\forall int i; 0 <= i && i < rows; pieces[i].length == columns);
    //@ public invariant (\forall int i; 0 <= i && i < rows;  (\elemtype(\typeof(pieces[i])) == \type(ChessPiece)));


    /*@ public normal_behavior
      @     ensures this.columns == 8;
      @     ensures this.rows == 8;
      @ pure
      @*/
    public Board() {

        this.rows = 8;
        this.columns = 8;
        pieces = new ChessPiece[rows][];

        /*@ loop_invariant 0 <= i && i <= rows;
          @ loop_invariant (\forall int k; 0 <= k && k < i; pieces[k] != null && pieces[k].length == columns && \elemtype(\typeof(pieces[k])) == \type(ChessPiece));
          @ loop_invariant (\forall int k; 0 <= k && k < i; (\forall int j; 0 <= j && j < columns; pieces[k][j] == null));
          @ decreasing rows - i;
          @*/
        for (int i = 0; i < rows; i++) {
            pieces[i] = new ChessPiece[columns];
        }
    }


    /*@ public normal_behavior
      @     ensures \result == this.pieces;
      @ pure
      @*/
    public ChessPiece[][] getChessPieces() {
        return pieces;
    }

    /*@ public normal_behavior
      @     ensures \result == this.rows;
      @ pure
      @*/
    public int getRows() {
        return rows;
    }

    /*@ public normal_behavior
      @     ensures \result == this.columns;
      @ pure
      @*/
    public int getColumns() {
        return columns;
    }

    /*@ public normal_behavior
      @     ensures \result == this.pieces;
      @ pure
      @*/
    public /*@ nullable*/ ChessPiece[][] getPieces() {
        return pieces;
    }

    /*@ public normal_behavior
          @     requires positionExistsBasic(row, column);
          @     ensures \result == pieces[row][column];
          @     assignable \nothing;
          @ also
          @ public exceptional_behavior
          @     requires !positionExistsBasic(row, column);
          @     signals_only RuntimeException;
          @     assignable \nothing;
          @*/
    public /*@ nullable */ ChessPiece piece(int row, int column) {

        if (!positionExistsBasic(row, column)) {
            //@ assert !positionExistsBasic(row, column);
            throw new BoardException("A posição está fora do tabuleiro.");
        }

        return pieces[row][column];
    }

    /*@ public normal_behavior
      @     requires position.row >= 0 && position.row < rows && position.column >= 0 && position.column < columns;
      @     ensures \result == pieces[position.row][position.column];
      @     assignable \nothing;
      @ also
      @ public exceptional_behavior
      @     requires position.row < 0 || position.row >= rows || position.column < 0 || position.column >= columns;
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public /*@ nullable */ ChessPiece piece(Position position) {

        if (!positionExists(position)) {
            //@ assert position.row < 0 || position.row >= rows || position.column < 0 || position.column >= columns;
            throw new BoardException("A posição está fora do tabuleiro.");
        }

        return pieces[position.getRow()][position.getColumn()];
    }

    /*@ public normal_behavior
      @     requires positionExists(position);
      @     requires pieces[position.row][position.column] == null;
      @     ensures position.row == \old(position.row);
      @     ensures position.column == \old(position.column);
      @     ensures (\forall int i; 0 <= i && i < rows;
      @                 \forall int j; 0 <= j < columns;
      @                     (i != position.row && j != position.column) ==> pieces[i][j] == \old(pieces[i][j]));
      @     ensures rows == \old(rows);
      @     ensures columns == \old(columns);
      @     ensures pieces == \old(pieces);
      @     ensures pieces[position.row][position.column] == piece;
      @     ensures piece.modelPosition == position;
      @ also
      @ public exceptional_behavior
      @     requires !positionExists(position) || (pieces[position.row][position.column] != null);
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public void placeChessPiece(ChessPiece piece, Position position) {
        if (thereIsAPiece(position)) {
            throw new BoardException("Já existe uma peça na posição " + position);
        }

        pieces[position.getRow()][position.getColumn()] = piece;
        piece.position = position;
        //@ assert piece.modelPosition.row < 8 && piece.modelPosition.column < 8;
    }


    /*@ public normal_behavior
      @     requires position.row >= 0;
      @     requires position.column >= 0;
      @     requires position.row < rows;
      @     requires position.column < columns;
      @     requires pieces[position.row][position.column] != null;
      @     ensures position.row == \old(position.row);
      @     ensures position.column == \old(position.column);
      @     ensures \result == (\old(pieces[position.row][position.column]));
      @     ensures pieces[position.row][position.column] == null;
      @     ensures (\forall int i; 0 <= i && i < rows;
      @                 \forall int j; 0 <= j < columns;
      @                     (i != position.row && j != position.column) ==>
                                pieces[i][j] == \old(pieces[i][j]));
      @     ensures rows == \old(rows);
      @     ensures columns == \old(columns);
      @     ensures pieces == \old(pieces);
      @ also
      @ public normal_behavior
      @     requires position.row >= 0;
      @     requires position.column >= 0;
      @     requires position.row < rows;
      @     requires position.column < columns;
      @     requires pieces[position.row][position.column] == null;
      @     ensures position.row == \old(position.row);
      @     ensures position.column == \old(position.column);
      @     ensures \result == null;
      @     assignable \nothing;
      @ also
      @ public normal_behavior
      @     requires !(position.row >= 0 && position.column >= 0 && position.row < rows &&
      @                position.column < columns);
      @     ensures position.row == \old(position.row);
      @     ensures position.column == \old(position.column);
      @     ensures \result == null;
      @     assignable \nothing;
      @*/
    public /*@ nullable */ ChessPiece removeChessPiece(Position position) {
        if (!positionExists(position)) {
            return null;
        }

        //@ assert position.row >= 0 && position.row < rows;
        //@ assert position.column >= 0 && position.column < columns;
        if (piece(position) == null) {
            return null;
        }

        ChessPiece aux = piece(position);
        aux.position = null;

        //@ assert pieces[position.getRow()][position.getColumn()] != null;
        pieces[position.getRow()][position.getColumn()] = null;

        return aux;
    }


    /*@ private normal_behavior
      @     requires row >= 0 && row < rows;
      @     requires column >= 0 && column < columns;
      @     ensures \result == true;
      @ also
      @ private normal_behavior
      @     requires row < 0 || row >= rows || column < 0 || column >= columns;
      @     ensures \result == false;
      @ spec_public
      @ pure helper
      @*/
    private boolean positionExistsBasic(int row, int column) {
        return row >= 0 && row < rows && column >= 0 && column < columns;
    }

    /*@ public normal_behavior
      @     ensures \result == (position.row >= 0 && position.row < this.rows
      @                    && position.column >= 0 && position.column < this.columns);
      @ pure
      @*/
    public boolean positionExists(Position position) {
        int row = position.getRow();
        int column = position.getColumn();
        return positionExistsBasic(row, column);
    }


    /*@ public normal_behavior
      @     requires position.row >= 0 && position.row < rows && position.column >= 0 && position.column < columns;
      @     requires pieces[position.row][position.column] != null;
      @     ensures \result == true;
      @     assignable \nothing;
      @ also
      @ public normal_behavior
      @     requires position.row >= 0 && position.row < rows && position.column >= 0 && position.column < columns;
      @     requires pieces[position.row][position.column] == null;
      @     ensures \result == false;
      @     assignable \nothing;
      @ also
      @ public exceptional_behavior
      @     requires position.row < 0 || position.row >= rows || position.column < 0 || position.column >= columns;
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public boolean thereIsAPiece(Position position) {

        if (!positionExists(position)) {
            throw new BoardException("A posição fora do tabuleiro");
        }
        return piece(position) != null;
    }
}