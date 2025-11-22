package model.gestoreService;

import model.ConPool;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedStatic;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

class GestoreDAOTest {

    private GestoreDAO gestoreDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;

    @BeforeEach
    void setUp() {
        gestoreDAO = new GestoreDAO();
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
    }

    // ==================== Tests for doSave ====================

    @Test
    void testDoSave_Success() throws SQLException {
        Gestore gestore = new Gestore();
        gestore.setMatricola("MAT001");
        gestore.setStipendio(2500.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> gestoreDAO.doSave(gestore));

            verify(mockConnection).prepareStatement("INSERT INTO Gestore (matricola, stipendio) VALUES(?,?)");
            verify(mockPreparedStatement).setString(1, "MAT001");
            verify(mockPreparedStatement).setDouble(2, 2500.0);
        }
    }

    @Test
    void testDoSave_InsertError() throws SQLException {
        Gestore gestore = new Gestore();
        gestore.setMatricola("MAT002");
        gestore.setStipendio(3000.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, () -> gestoreDAO.doSave(gestore));
            assertEquals("INSERT error.", exception.getMessage());
        }
    }

    @Test
    void testDoSave_SQLExceptionThrown() throws SQLException {
        Gestore gestore = new Gestore();
        gestore.setMatricola("MAT003");
        gestore.setStipendio(2800.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Connection error"));

            assertThrows(RuntimeException.class, () -> gestoreDAO.doSave(gestore));
        }
    }

    // ==================== Tests for deleteGestore ====================

    @Test
    void testDeleteGestore_Success() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> gestoreDAO.deleteGestore("MAT001"));

            verify(mockConnection).prepareStatement("DELETE FROM Gestore WHERE matricola=?");
            verify(mockPreparedStatement).setString(1, "MAT001");
        }
    }

    @Test
    void testDeleteGestore_NoRowsDeleted() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, () -> gestoreDAO.deleteGestore("MAT_NONEXISTENT"));
            assertEquals("DELETE error.", exception.getMessage());
        }
    }

    @Test
    void testDeleteGestore_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("DB error"));

            assertThrows(RuntimeException.class, () -> gestoreDAO.deleteGestore("MAT001"));
        }
    }

    // ==================== Tests for updateGestore ====================

    @Test
    void testUpdateGestore_Success() throws SQLException {
        Gestore gestore = new Gestore();
        gestore.setMatricola("MAT001");
        gestore.setStipendio(3500.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> gestoreDAO.updateGestore(gestore));

            verify(mockConnection).prepareStatement("UPDATE Gestore SET stipendio = ? WHERE matricola = ?");
            verify(mockPreparedStatement).setDouble(1, 3500.0);
            verify(mockPreparedStatement).setString(2, "MAT001");
        }
    }

    @Test
    void testUpdateGestore_NoRowsUpdated() throws SQLException {
        Gestore gestore = new Gestore();
        gestore.setMatricola("MAT_NONEXISTENT");
        gestore.setStipendio(2000.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, () -> gestoreDAO.updateGestore(gestore));
            assertEquals("UPDATE error.", exception.getMessage());
        }
    }

    @Test
    void testUpdateGestore_SQLExceptionThrown() throws SQLException {
        Gestore gestore = new Gestore();
        gestore.setMatricola("MAT001");
        gestore.setStipendio(3000.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Update failed"));

            assertThrows(RuntimeException.class, () -> gestoreDAO.updateGestore(gestore));
        }
    }

    // ==================== Tests for doRetrivedAll ====================

    @Test
    void testDoRetrivedAll_MultipleGestori() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next())
                    .thenReturn(true)
                    .thenReturn(true)
                    .thenReturn(true)
                    .thenReturn(false);
            when(mockResultSet.getString(1))
                    .thenReturn("MAT001")
                    .thenReturn("MAT002")
                    .thenReturn("MAT003");
            when(mockResultSet.getDouble(2))
                    .thenReturn(2500.0)
                    .thenReturn(3000.0)
                    .thenReturn(2800.0);

            List<Gestore> result = gestoreDAO.doRetrivedAll();

            assertNotNull(result);
            assertEquals(3, result.size());
            assertEquals("MAT001", result.get(0).getMatricola());
            assertEquals(2500.0, result.get(0).getStipendio());
            assertEquals("MAT002", result.get(1).getMatricola());
            assertEquals(3000.0, result.get(1).getStipendio());
            assertEquals("MAT003", result.get(2).getMatricola());
            assertEquals(2800.0, result.get(2).getStipendio());
            verify(mockConnection).prepareStatement("SELECT * FROM Gestore");
        }
    }

    @Test
    void testDoRetrivedAll_Empty() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            List<Gestore> result = gestoreDAO.doRetrivedAll();

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }
    }

    @Test
    void testDoRetrivedAll_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query failed"));

            assertThrows(RuntimeException.class, () -> gestoreDAO.doRetrivedAll());
        }
    }

    // ==================== Tests for doRetrieveById ====================

    @Test
    void testDoRetrieveById_Success() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next()).thenReturn(true);
            when(mockResultSet.getString(1)).thenReturn("MAT001");
            when(mockResultSet.getDouble(2)).thenReturn(2500.0);

            Gestore result = gestoreDAO.doRetrieveById("MAT001");

            assertNotNull(result);
            assertEquals("MAT001", result.getMatricola());
            assertEquals(2500.0, result.getStipendio());
            verify(mockPreparedStatement).setString(1, "MAT001");
        }
    }

    @Test
    void testDoRetrieveById_NotFound() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            Gestore result = gestoreDAO.doRetrieveById("MAT_NONEXISTENT");

            assertNull(result);
            verify(mockPreparedStatement).setString(1, "MAT_NONEXISTENT");
        }
    }

    @Test
    void testDoRetrieveById_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query error"));

            assertThrows(RuntimeException.class, () -> gestoreDAO.doRetrieveById("MAT001"));
        }
    }

    // ==================== Integration Tests ====================

    @Test
    void testFullGestoreLifecycle() throws SQLException {
        Gestore gestore = new Gestore();
        gestore.setMatricola("MAT_LIFECYCLE");
        gestore.setStipendio(2500.0);

        // Test save
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> gestoreDAO.doSave(gestore));
        }

        // Test update
        gestore.setStipendio(3500.0);
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> gestoreDAO.updateGestore(gestore));
        }

        // Test retrieve
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(true);
            when(mockResultSet.getString(1)).thenReturn("MAT_LIFECYCLE");
            when(mockResultSet.getDouble(2)).thenReturn(3500.0);

            Gestore result = gestoreDAO.doRetrieveById("MAT_LIFECYCLE");
            assertNotNull(result);
            assertEquals("MAT_LIFECYCLE", result.getMatricola());
            assertEquals(3500.0, result.getStipendio());
        }

        // Test delete
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> gestoreDAO.deleteGestore("MAT_LIFECYCLE"));
        }
    }

    // ==================== Edge Case Tests ====================

    @Test
    void testDoSave_WithZeroStipendio() throws SQLException {
        Gestore gestore = new Gestore();
        gestore.setMatricola("MAT_ZERO");
        gestore.setStipendio(0.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> gestoreDAO.doSave(gestore));
            verify(mockPreparedStatement).setDouble(2, 0.0);
        }
    }

    @Test
    void testUpdateGestore_WithHighStipendio() throws SQLException {
        Gestore gestore = new Gestore();
        gestore.setMatricola("MAT_HIGH");
        gestore.setStipendio(99999.99);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> gestoreDAO.updateGestore(gestore));
            verify(mockPreparedStatement).setDouble(1, 99999.99);
        }
    }
}
