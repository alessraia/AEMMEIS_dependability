package model.utenteService;

import model.ConPool;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.carrelloService.RigaCarrelloDAO;
import model.ordineService.OrdineDAO;
import model.tesseraService.Tessera;
import model.tesseraService.TesseraDAO;
import org.junit.jupiter.api.*;
import org.mockito.MockedStatic;
import org.mindrot.jbcrypt.BCrypt;

import java.sql.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test class for UtenteDAO
 * Tests all CRUD operations and user management methods
 */
class UtenteDAOTest {

    private UtenteDAO utenteDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;
    private MockedStatic<ConPool> mockedConPool;
    private TesseraDAO mockTesseraDAO;
    private RigaCarrelloDAO mockRigaCarrelloDAO;
    private CarrelloDAO mockCarrelloDAO;
    private OrdineDAO mockOrdineDAO;

    @BeforeEach
    void setUp() throws SQLException {
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
        mockTesseraDAO = mock(TesseraDAO.class);
        mockRigaCarrelloDAO = mock(RigaCarrelloDAO.class);
        mockCarrelloDAO = mock(CarrelloDAO.class);
        mockOrdineDAO = mock(OrdineDAO.class);

        utenteDAO = new UtenteDAO(mockTesseraDAO, mockRigaCarrelloDAO, mockCarrelloDAO, mockOrdineDAO);

        mockedConPool = mockStatic(ConPool.class);
        mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
    }

    @AfterEach
    void tearDown() {
        if (mockedConPool != null) {
            mockedConPool.close();
        }
    }

    // ==================== doRetrieveById Tests ====================

    @Test
    void testDoRetrieveById_Found() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String hashedPassword = "e24114b7e08681dc91c43a0a76e8b7c14f8c2fb8"; // SHA-1 hash of "password123"
        List<String> telefoni = Arrays.asList("1234567890", "0987654321");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getString(1)).thenReturn("Mario Rossi", "1234567890");
        when(mockResultSet.getString(2)).thenReturn("test@example.com");
        when(mockResultSet.getString(3)).thenReturn(hashedPassword);
        when(mockResultSet.getString(4)).thenReturn("premium");

        UtenteDAO spyDAO = spy(utenteDAO);
        doReturn(telefoni).when(spyDAO).cercaTelefoni(email);

        // Act
        Utente result = spyDAO.doRetrieveById(email);

        // Assert
        assertNotNull(result);
        assertEquals("Mario Rossi", result.getNomeUtente());
        assertEquals("test@example.com", result.getEmail());
        assertEquals(hashedPassword, result.getCodiceSicurezza());
        assertEquals("premium", result.getTipo());
        assertEquals(telefoni, result.getTelefoni());
        verify(mockPreparedStatement).setString(1, email);
    }

    @Test
    void testDoRetrieveById_NotFound() throws SQLException {
        // Arrange
        String email = "notfound@example.com";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        Utente result = utenteDAO.doRetrieveById(email);

        // Assert
        assertNull(result);
        verify(mockPreparedStatement).setString(1, email);
    }

    @Test
    void testDoRetrieveById_SQLException() throws SQLException {
        // Arrange
        String email = "test@example.com";
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> utenteDAO.doRetrieveById(email));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doRetrieveByEmailPassword Tests ====================

    @Test
    void testDoRetrieveByEmailPassword_Found() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String plainPassword = "test_password_" + System.currentTimeMillis();// password in plain text
        String bcryptHash = BCrypt.hashpw(plainPassword, BCrypt.gensalt());; // bcrypt hash of "password123"
        List<String> telefoni = Arrays.asList("1234567890");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getString("nomeUtente")).thenReturn("Mario Rossi");
        when(mockResultSet.getString("email")).thenReturn("test@example.com");
        when(mockResultSet.getString("codiceSicurezza")).thenReturn(bcryptHash);
        when(mockResultSet.getString("tipo")).thenReturn("base");

        UtenteDAO spyDAO = spy(utenteDAO);
        doReturn(telefoni).when(spyDAO).cercaTelefoni(email);

        // Mock BCrypt.checkpw to return true for the correct password
        MockedStatic<BCrypt> mockedBCrypt = mockStatic(BCrypt.class);
        mockedBCrypt.when(() -> BCrypt.checkpw(plainPassword, bcryptHash)).thenReturn(true);

        try {
            // Act
            Utente result = spyDAO.doRetrieveByEmailPassword(email, plainPassword);

            // Assert
            assertNotNull(result);
            assertEquals("Mario Rossi", result.getNomeUtente());
            assertEquals("test@example.com", result.getEmail());
            assertEquals(bcryptHash, result.getCodiceSicurezza());
            assertEquals("base", result.getTipo());
            assertEquals(telefoni, result.getTelefoni());
            verify(mockPreparedStatement).setString(1, email);
        } finally {
            mockedBCrypt.close();
        }
    }

    @Test
    void testDoRetrieveByEmailPassword_NotFound() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String wrongPassword = "wronghash1234567890abcdef1234567890abcd";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        Utente result = utenteDAO.doRetrieveByEmailPassword(email, wrongPassword);

        // Assert
        assertNull(result);
    }

    @Test
    void testDoRetrieveByEmailPassword_SQLException() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String hashedPassword = "e24114b7e08681dc91c43a0a76e8b7c14f8c2fb8";
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.doRetrieveByEmailPassword(email, hashedPassword));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doSave Tests ====================

    @Test
    void testDoSave_Success() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        UtenteDAO spyDAO = spy(utenteDAO);
        doNothing().when(spyDAO).addTelefono(anyString(), anyString());

        // Act
        assertDoesNotThrow(() -> spyDAO.doSave(utente));

        // Assert
        verify(mockPreparedStatement).setString(1, "Mario Rossi");
        verify(mockPreparedStatement).setString(2, "test@example.com");
        // Note: We can't verify the exact bcrypt hash (parameter 3) since bcrypt uses random salt
        // Instead, we verify it's a non-null bcrypt hash by using anyString()
        verify(mockPreparedStatement).setString(eq(3), anyString());
        verify(mockPreparedStatement).setString(4, "base");
        verify(mockPreparedStatement).executeUpdate();
        verify(spyDAO, times(2)).addTelefono(eq("test@example.com"), anyString());
    }

    @Test
    void testDoSave_InsertFails() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> utenteDAO.doSave(utente));
        assertEquals("INSERT error.", exception.getMessage());
    }

    @Test
    void testDoSave_SQLException() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> utenteDAO.doSave(utente));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doRetrieveAll Tests ====================

    @Test
    void testDoRetrieveAll_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getString(1)).thenReturn("Mario Rossi", "Luigi Verdi");
        when(mockResultSet.getString(2)).thenReturn("mario@example.com", "luigi@example.com");
        when(mockResultSet.getString(3)).thenReturn("e24114b7e08681dc91c43a0a76e8b7c14f8c2fb8", "a94a8fe5ccb19ba61c4c0873d391e987982fbbd3");
        when(mockResultSet.getString(4)).thenReturn("base", "premium");

        // Act
        List<Utente> result = utenteDAO.doRetrieveAll();

        // Assert
        assertNotNull(result);
        assertEquals(2, result.size());
        
        // Verify rs.next() was called exactly 3 times (2x true, 1x false)
        // This kills the "negated conditional" mutation on line 155
        verify(mockResultSet, times(3)).next();
        
        assertEquals("Mario Rossi", result.get(0).getNomeUtente());
        assertEquals("mario@example.com", result.get(0).getEmail());
        assertEquals("e24114b7e08681dc91c43a0a76e8b7c14f8c2fb8", result.get(0).getCodiceSicurezza());
        assertEquals("base", result.get(0).getTipo());
        assertEquals("Luigi Verdi", result.get(1).getNomeUtente());
        assertEquals("luigi@example.com", result.get(1).getEmail());
        assertEquals("a94a8fe5ccb19ba61c4c0873d391e987982fbbd3", result.get(1).getCodiceSicurezza());
        assertEquals("premium", result.get(1).getTipo());
    }

    @Test
    void testDoRetrieveAll_EmptyResult() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<Utente> result = utenteDAO.doRetrieveAll();

        // Assert
        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @Test
    void testDoRetrieveAll_SQLException() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> utenteDAO.doRetrieveAll());
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== updateUtente Tests ====================

    @Test
    void testUpdateUtente_Success() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();
        List<String> existingTelefoni = Arrays.asList("1234567890");

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        UtenteDAO spyDAO = spy(utenteDAO);
        doReturn(existingTelefoni).when(spyDAO).cercaTelefoni("test@example.com");
        doNothing().when(spyDAO).addTelefono(anyString(), anyString());
        doNothing().when(spyDAO).deleteTelefono(anyString(), anyString());

        // Act
        assertDoesNotThrow(() -> spyDAO.updateUtente(utente));

        // Assert
        verify(mockPreparedStatement).setString(1, "Mario Rossi");
        verify(mockPreparedStatement).setString(2, "base");
        verify(mockPreparedStatement).setString(3, "test@example.com");
        verify(mockPreparedStatement).executeUpdate();
        // Verify that new phone was added (0987654321)
        verify(spyDAO).addTelefono("test@example.com", "0987654321");
    }

    @Test
    void testUpdateUtente_WithPhoneDeletion() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();
        utente.setTelefoni(Arrays.asList("1234567890")); // Only one phone now
        List<String> existingTelefoni = Arrays.asList("1234567890", "0987654321"); // Two phones in DB

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        UtenteDAO spyDAO = spy(utenteDAO);
        doReturn(existingTelefoni).when(spyDAO).cercaTelefoni("test@example.com");
        doNothing().when(spyDAO).addTelefono(anyString(), anyString());
        doNothing().when(spyDAO).deleteTelefono(anyString(), anyString());

        // Act
        assertDoesNotThrow(() -> spyDAO.updateUtente(utente));

        // Assert
        verify(mockPreparedStatement).setString(1, "Mario Rossi");
        verify(mockPreparedStatement).setString(2, "base");
        verify(mockPreparedStatement).setString(3, "test@example.com");
        verify(mockPreparedStatement).executeUpdate();
        // Verify that phone 0987654321 was deleted
        verify(spyDAO).deleteTelefono("test@example.com", "0987654321");
        // Verify that addTelefono was never called (no new phones)
        verify(spyDAO, never()).addTelefono(anyString(), eq("0987654321"));
    }

    @Test
    void testUpdateUtente_UpdateFails() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> utenteDAO.updateUtente(utente));
        assertEquals("UPDATE error.", exception.getMessage());
    }

    @Test
    void testUpdateUtente_SQLException() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, () -> utenteDAO.updateUtente(utente));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== updateUtentePassword Tests ====================

    @Test
    void testUpdateUtentePassword_Success() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();
        String newPassword = "newHashedPassword123";
        utente.setCodiceSicurezza(newPassword);

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> utenteDAO.updateUtentePassword(utente));

        // Assert
        // Note: We can't verify the exact bcrypt hash since bcrypt uses random salt
        // Instead, we verify it's a non-null bcrypt hash by using anyString()
        verify(mockPreparedStatement).setString(eq(1), anyString());
        verify(mockPreparedStatement).setString(2, "test@example.com");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testUpdateUtentePassword_UpdateFails() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.updateUtentePassword(utente));
        assertEquals("UPDATE error.", exception.getMessage());
    }

    @Test
    void testUpdateUtentePassword_SQLException() throws SQLException {
        // Arrange
        Utente utente = createValidUtente();

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.updateUtentePassword(utente));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== deleteTelefono Tests ====================

    @Test
    void testDeleteTelefono_Success() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String telefono = "1234567890";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> utenteDAO.deleteTelefono(email, telefono));

        // Assert
        verify(mockPreparedStatement).setString(1, email);
        verify(mockPreparedStatement).setString(2, telefono);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteTelefono_DeleteFails() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String telefono = "1234567890";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.deleteTelefono(email, telefono));
        assertEquals("DELETE error.", exception.getMessage());
    }

    @Test
    void testDeleteTelefono_SQLException() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String telefono = "1234567890";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.deleteTelefono(email, telefono));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== deleteTelefoni Tests ====================

    @Test
    void testDeleteTelefoni_Success() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(2);

        // Act
        assertDoesNotThrow(() -> utenteDAO.deleteTelefoni(email));

        // Assert
        verify(mockPreparedStatement).setString(1, email);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteTelefoni_OneRowDeleted() throws SQLException {
        // Arrange - Test boundary case: exactly 1 row deleted
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act - should succeed with 1 row deleted
        assertDoesNotThrow(() -> utenteDAO.deleteTelefoni(email));

        // Assert
        verify(mockPreparedStatement).setString(1, email);
        verify(mockPreparedStatement).executeUpdate();
        
        // This test kills the "changed conditional boundary" mutation on line 289
        // Mutant: if(ps.executeUpdate() <= 1) would fail this test
        // because it would throw exception when executeUpdate() returns 1
    }

    @Test
    void testDeleteTelefoni_NoRowsDeleted() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.deleteTelefoni(email));
        assertTrue(exception.getMessage().contains("DELETE error"));
    }

    @Test
    void testDeleteTelefoni_SQLException() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.deleteTelefoni(email));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== addTelefono Tests ====================

    @Test
    void testAddTelefono_Success() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String telefono = "1234567890";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> utenteDAO.addTelefono(email, telefono));

        // Assert
        verify(mockPreparedStatement).setString(1, telefono);
        verify(mockPreparedStatement).setString(2, email);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testAddTelefono_InsertFails() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String telefono = "1234567890";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.addTelefono(email, telefono));
        assertEquals("INSERT error.", exception.getMessage());
    }

    @Test
    void testAddTelefono_SQLException() throws SQLException {
        // Arrange
        String email = "test@example.com";
        String telefono = "1234567890";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.addTelefono(email, telefono));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== cercaTelefoni Tests ====================

    @Test
    void testCercaTelefoni_Success() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getString(1)).thenReturn("1234567890", "0987654321");

        // Act
        List<String> result = utenteDAO.cercaTelefoni(email);

        // Assert
        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals("1234567890", result.get(0));
        assertEquals("0987654321", result.get(1));
        verify(mockPreparedStatement).setString(1, email);
    }

    @Test
    void testCercaTelefoni_EmptyResult() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<String> result = utenteDAO.cercaTelefoni(email);

        // Assert
        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @Test
    void testCercaTelefoni_SQLException() throws SQLException {
        // Arrange
        String email = "test@example.com";

        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.cercaTelefoni(email));
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== doRetrieveAllTelefoni Tests ====================

    @Test
    void testDoRetrieveAllTelefoni_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, true, false);
        when(mockResultSet.getString(1)).thenReturn("1234567890", "0987654321", "1111111111");

        // Act
        List<String> result = utenteDAO.doRetrieveAllTelefoni();

        // Assert
        assertNotNull(result);
        assertEquals(3, result.size());
        assertEquals("1234567890", result.get(0));
        assertEquals("0987654321", result.get(1));
        assertEquals("1111111111", result.get(2));
    }

    @Test
    void testDoRetrieveAllTelefoni_EmptyResult() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<String> result = utenteDAO.doRetrieveAllTelefoni();

        // Assert
        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @Test
    void testDoRetrieveAllTelefoni_SQLException() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Database error"));

        // Act & Assert
        RuntimeException exception = assertThrows(RuntimeException.class, 
            () -> utenteDAO.doRetrieveAllTelefoni());
        assertTrue(exception.getCause() instanceof SQLException);
    }

    // ==================== Helper Methods ====================

    private Utente createValidUtente() {
        Utente utente = new Utente();
        utente.setNomeUtente("Mario Rossi");
        utente.setEmail("test@example.com");
        utente.setCodiceSicurezza("password123");
        utente.setTipo("base");
        utente.setTelefoni(Arrays.asList("1234567890", "0987654321"));
        return utente;
    }
}
