package model.carrelloService;

import model.ConPool;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedStatic;
import org.mockito.MockedConstruction;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

class CarrelloDAOTest {

    private CarrelloDAO carrelloDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;

    @BeforeEach
    void setUp() {
        carrelloDAO = new CarrelloDAO();
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
    }

    // ==================== Tests for doSave ====================

    @Test
    void testDoSave_Success() throws SQLException {
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CARR001");
        carrello.setEmail("test@example.com");
        carrello.setTotale(100.50);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> carrelloDAO.doSave(carrello));

            verify(mockConnection).prepareStatement("INSERT INTO Carrello (idCarrello, totale, email) VALUES(?,?,?)");
            verify(mockPreparedStatement).setString(1, "CARR001");
            verify(mockPreparedStatement).setDouble(2, 100.50);
            verify(mockPreparedStatement).setString(3, "test@example.com");
            verify(mockPreparedStatement).executeUpdate();
        }
    }

    @Test
    void testDoSave_InsertError() throws SQLException {
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CARR002");
        carrello.setEmail("test2@example.com");
        carrello.setTotale(50.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0); // Error: no rows affected

            RuntimeException exception = assertThrows(RuntimeException.class, () -> carrelloDAO.doSave(carrello));
            assertEquals("INSERT error.", exception.getMessage());
        }
    }

    @Test
    void testDoSave_SQLExceptionThrown() throws SQLException {
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CARR003");
        carrello.setEmail("test3@example.com");
        carrello.setTotale(75.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Connection error"));

            assertThrows(RuntimeException.class, () -> carrelloDAO.doSave(carrello));
        }
    }

    // ==================== Tests for deleteCarrello ====================

    @Test
    void testDeleteCarrello_Success() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> carrelloDAO.deleteCarrello("CARR001"));

            verify(mockConnection).prepareStatement("DELETE FROM Carrello WHERE idCarrello=?");
            verify(mockPreparedStatement).setString(1, "CARR001");
            verify(mockPreparedStatement).executeUpdate();
        }
    }

    @Test
    void testDeleteCarrello_NoRowsDeleted() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0); // No rows deleted

            RuntimeException exception = assertThrows(RuntimeException.class, () -> carrelloDAO.deleteCarrello("NONEXISTENT"));
            assertEquals("DELETE error.", exception.getMessage());
        }
    }

    @Test
    void testDeleteCarrello_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("DB error"));

            assertThrows(RuntimeException.class, () -> carrelloDAO.deleteCarrello("CARR001"));
        }
    }

    // ==================== Tests for updateCarrello ====================

    @Test
    void testUpdateCarrello_Success() throws SQLException {
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CARR001");
        carrello.setTotale(250.75);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> carrelloDAO.updateCarrello(carrello));

            verify(mockConnection).prepareStatement("UPDATE Carrello SET totale = ? WHERE idCarrello = ?");
            verify(mockPreparedStatement).setDouble(1, 250.75);
            verify(mockPreparedStatement).setString(2, "CARR001");
            verify(mockPreparedStatement).executeUpdate();
        }
    }

    @Test
    void testUpdateCarrello_NoRowsUpdated() throws SQLException {
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("NONEXISTENT");
        carrello.setTotale(100.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, () -> carrelloDAO.updateCarrello(carrello));
            assertEquals("UPDATE error.", exception.getMessage());
        }
    }

    @Test
    void testUpdateCarrello_SQLExceptionThrown() throws SQLException {
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CARR001");
        carrello.setTotale(100.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Update error"));

            assertThrows(RuntimeException.class, () -> carrelloDAO.updateCarrello(carrello));
        }
    }

    // ==================== Tests for doRetriveById ====================

    @Test
    void testDoRetriveById_Success() throws SQLException {
        List<RigaCarrello> righeCarrello = new ArrayList<>();
        RigaCarrello riga1 = new RigaCarrello();
        righeCarrello.add(riga1);
        
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class);
             MockedConstruction<RigaCarrelloDAO> mockedRiga = mockConstruction(RigaCarrelloDAO.class, 
                (mock, context) -> when(mock.doRetrieveByIdCarrello(anyString())).thenReturn(righeCarrello))) {
            
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next()).thenReturn(true);
            when(mockResultSet.getString(1)).thenReturn("CARR001");
            when(mockResultSet.getDouble(2)).thenReturn(150.0);
            when(mockResultSet.getString(3)).thenReturn("user@example.com");

            Carrello result = carrelloDAO.doRetriveById("CARR001");

            assertNotNull(result);
            assertEquals("CARR001", result.getIdCarrello());
            assertEquals(150.0, result.getTotale());
            assertEquals("user@example.com", result.getEmail());
            assertNotNull(result.getRigheCarrello());
            assertEquals(1, result.getRigheCarrello().size());
            verify(mockPreparedStatement).setString(1, "CARR001");
        }
    }

    @Test
    void testDoRetriveById_NotFound() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            Carrello result = carrelloDAO.doRetriveById("NONEXISTENT");

            assertNull(result);
            verify(mockPreparedStatement).setString(1, "NONEXISTENT");
        }
    }

    @Test
    void testDoRetriveById_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query error"));

            assertThrows(RuntimeException.class, () -> carrelloDAO.doRetriveById("CARR001"));
        }
    }

    // ==================== Tests for doRetriveByUtente ====================

    @Test
    void testDoRetriveByUtente_Success() throws SQLException {
        List<RigaCarrello> righeCarrello = new ArrayList<>();
        RigaCarrello riga1 = new RigaCarrello();
        righeCarrello.add(riga1);
        
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class);
             MockedConstruction<RigaCarrelloDAO> mockedRiga = mockConstruction(RigaCarrelloDAO.class,
                (mock, context) -> when(mock.doRetrieveByIdCarrello(anyString())).thenReturn(righeCarrello))) {
            
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next()).thenReturn(true);
            when(mockResultSet.getString(1)).thenReturn("CARR002");
            when(mockResultSet.getDouble(2)).thenReturn(200.0);
            when(mockResultSet.getString(3)).thenReturn("mario@example.com");

            Carrello result = carrelloDAO.doRetriveByUtente("mario@example.com");

            assertNotNull(result);
            assertEquals("CARR002", result.getIdCarrello());
            assertEquals(200.0, result.getTotale());
            assertEquals("mario@example.com", result.getEmail());
            assertNotNull(result.getRigheCarrello());
            assertEquals(1, result.getRigheCarrello().size());
            verify(mockPreparedStatement).setString(1, "mario@example.com");
        }
    }

    @Test
    void testDoRetriveByUtente_NotFound() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            Carrello result = carrelloDAO.doRetriveByUtente("nonexistent@example.com");

            assertNull(result);
            verify(mockPreparedStatement).setString(1, "nonexistent@example.com");
        }
    }

    @Test
    void testDoRetriveByUtente_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

            assertThrows(RuntimeException.class, () -> carrelloDAO.doRetriveByUtente("test@example.com"));
        }
    }

    // ==================== Tests for doRetrivedAllIdCarrelli ====================

    @Test
    void testDoRetrivedAllIdCarrelli_Success() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next())
                    .thenReturn(true)  // First row
                    .thenReturn(true)  // Second row
                    .thenReturn(true)  // Third row
                    .thenReturn(false); // No more rows
            when(mockResultSet.getString(1))
                    .thenReturn("CARR001")
                    .thenReturn("CARR002")
                    .thenReturn("CARR003");

            List<String> result = carrelloDAO.doRetrivedAllIdCarrelli();

            assertNotNull(result);
            assertEquals(3, result.size());
            assertTrue(result.contains("CARR001"));
            assertTrue(result.contains("CARR002"));
            assertTrue(result.contains("CARR003"));
            verify(mockConnection).prepareStatement("SELECT * FROM Carrello");
            verify(mockResultSet, times(4)).next(); // Verify the loop termination
        }
    }

    @Test
    void testDoRetrivedAllIdCarrelli_Empty() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false); // No rows

            List<String> result = carrelloDAO.doRetrivedAllIdCarrelli();

            assertNotNull(result);
            assertTrue(result.isEmpty());
            assertEquals(0, result.size());
            verify(mockResultSet, times(1)).next(); // Verify loop termination on empty result
        }
    }

    @Test
    void testDoRetrivedAllIdCarrelli_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query failed"));

            assertThrows(RuntimeException.class, () -> carrelloDAO.doRetrivedAllIdCarrelli());
        }
    }
    
    @Test
    void testDoRetrivedAllIdCarrelli_SingleRow() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            
            when(mockResultSet.next())
                    .thenReturn(true)  // First row
                    .thenReturn(false); // No more rows
            when(mockResultSet.getString(1)).thenReturn("CARR_SINGLE");

            List<String> result = carrelloDAO.doRetrivedAllIdCarrelli();

            assertNotNull(result);
            assertEquals(1, result.size());
            assertEquals("CARR_SINGLE", result.get(0));
            verify(mockResultSet, times(2)).next(); // Called twice: once for the item, once to exit
        }
    }

    // ==================== Integration-like Tests ====================

    @Test
    void testFullCarrelloLifecycle() throws SQLException {
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CARR_TEST");
        carrello.setEmail("test@lifecycle.com");
        carrello.setTotale(99.99);

        // Test save
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> carrelloDAO.doSave(carrello));
        }

        // Test update
        carrello.setTotale(150.00);
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> carrelloDAO.updateCarrello(carrello));
        }

        // Test delete
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> carrelloDAO.deleteCarrello("CARR_TEST"));
        }
    }

    // ==================== Edge Case Tests ====================

    @Test
    void testDoSave_ZeroTotal() throws SQLException {
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CARR_ZERO");
        carrello.setEmail("zero@example.com");
        carrello.setTotale(0.0);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> carrelloDAO.doSave(carrello));
            verify(mockPreparedStatement).setDouble(2, 0.0);
        }
    }

    @Test
    void testUpdateCarrello_WithLargeTotal() throws SQLException {
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CARR_LARGE");
        carrello.setTotale(99999.99);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> carrelloDAO.updateCarrello(carrello));
            verify(mockPreparedStatement).setDouble(1, 99999.99);
        }
    }
}
