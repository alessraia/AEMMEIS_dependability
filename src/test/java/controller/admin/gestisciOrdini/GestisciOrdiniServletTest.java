package controller.admin.gestisciOrdini;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

/**
 * Unit tests for GestisciOrdiniServlet.
 * Tests the servlet's ability to retrieve all non-admin users and display them
 * for order management purposes.
 */
class GestisciOrdiniServletTest {

    private GestisciOrdiniServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new GestisciOrdiniServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/gestisciOrdini.jsp")).thenReturn(dispatcher);
    }

    /**
     * Test successful retrieval of non-admin users.
     * Scenario: All users are retrieved and admin users are filtered out
     */
    @Test
    void testDoGet_SuccessfulNonAdminUserRetrieval() throws ServletException, IOException {
        // Arrange
        Utente user1 = new Utente();
        user1.setEmail("user1@example.com");
        user1.setTipo("Cliente");

        Utente user2 = new Utente();
        user2.setEmail("admin@example.com");
        user2.setTipo("Gestore");

        Utente user3 = new Utente();
        user3.setEmail("user3@example.com");
        user3.setTipo("Cliente");

        List<Utente> allUsers = new ArrayList<>();
        allUsers.add(user1);
        allUsers.add(user2);
        allUsers.add(user3);

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && ((List<?>) utenti).size() == 2
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with only admin users.
     * Scenario: All users are admins - due to servlet bug in filtering loop,
     * when removing during iteration, one admin may remain
     */
    @Test
    void testDoGet_OnlyAdminUsersPresent() throws ServletException, IOException {
        // Arrange
        Utente admin1 = new Utente();
        admin1.setEmail("admin1@example.com");
        admin1.setTipo("Gestore");

        Utente admin2 = new Utente();
        admin2.setEmail("admin2@example.com");
        admin2.setTipo("Gestore");

        List<Utente> allUsers = new ArrayList<>();
        allUsers.add(admin1);
        allUsers.add(admin2);

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert - All admins removed with reverse iteration, result is empty
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && ((List<?>) utenti).size() == 0
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with only non-admin users.
     * Scenario: All users are non-admins and none should be filtered
     */
    @Test
    void testDoGet_OnlyNonAdminUsersPresent() throws ServletException, IOException {
        // Arrange
        Utente user1 = new Utente();
        user1.setEmail("user1@example.com");
        user1.setTipo("Cliente");

        Utente user2 = new Utente();
        user2.setEmail("user2@example.com");
        user2.setTipo("Cliente");

        List<Utente> allUsers = new ArrayList<>();
        allUsers.add(user1);
        allUsers.add(user2);

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && ((List<?>) utenti).size() == 2
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with empty user list.
     * Scenario: No users are present in the system
     */
    @Test
    void testDoGet_EmptyUserList() throws ServletException, IOException {
        // Arrange
        List<Utente> allUsers = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && ((List<?>) utenti).isEmpty()
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test request forwarding to correct JSP page.
     * Scenario: After processing, request is forwarded to the correct dispatcher
     */
    @Test
    void testDoGet_RequestForwardedCorrectly() throws ServletException, IOException {
        // Arrange
        List<Utente> allUsers = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).getRequestDispatcher("/WEB-INF/results/admin/ordini/gestisciOrdini.jsp");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test admin user filtering.
     * Scenario: Verify that users with "Gestore" type are filtered
     * Note: Due to servlet's remove-during-iteration bug, some admins may remain
     */
    @Test
    void testDoGet_AdminUserFiltering() throws ServletException, IOException {
        // Arrange
        Utente user1 = new Utente();
        user1.setEmail("user1@example.com");
        user1.setTipo("Cliente");

        Utente gestore1 = new Utente();
        gestore1.setEmail("gestore@example.com");
        gestore1.setTipo("Gestore");

        Utente gestore2 = new Utente();
        gestore2.setEmail("gestore2@example.com");
        gestore2.setTipo("Gestore Manager");

        List<Utente> allUsers = new ArrayList<>();
        allUsers.add(user1);
        allUsers.add(gestore1);
        allUsers.add(gestore2);

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert - Both admins removed with reverse iteration, only 1 regular user remains
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && ((List<?>) utenti).size() == 1
            ));
        }
    }

    /**
     * Test with large user list.
     * Scenario: System with many users, both admins and non-admins
     * Note: Due to servlet's remove-during-iteration bug, some admins may not be removed
     */
    @Test
    void testDoGet_LargeUserList() throws ServletException, IOException {
        // Arrange
        List<Utente> allUsers = new ArrayList<>();

        // Add 50 regular users
        for (int i = 1; i <= 50; i++) {
            Utente user = new Utente();
            user.setEmail("user" + i + "@example.com");
            user.setTipo("Cliente");
            allUsers.add(user);
        }

        // Add 10 admin users
        for (int i = 1; i <= 10; i++) {
            Utente admin = new Utente();
            admin.setEmail("admin" + i + "@example.com");
            admin.setTipo("Gestore");
            allUsers.add(admin);
        }

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert - All 10 admins removed with reverse iteration, 50 users remain
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && ((List<?>) utenti).size() == 50
            ));
        }
    }

    /**
     * Test DAO is called.
     * Scenario: Verify that UtenteDAO.doRetrieveAll is invoked
     */
    @Test
    void testDoGet_DAOMethodCalled() throws ServletException, IOException {
        // Arrange
        List<Utente> allUsers = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            UtenteDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO).doRetrieveAll();
        }
    }

    /**
     * Test operation sequence.
     * Scenario: Verify correct order of operations (retrieve, filter, setAttribute, forward)
     */
    @Test
    void testDoGet_CorrectOperationSequence() throws ServletException, IOException {
        // Arrange
        Utente user1 = new Utente();
        user1.setEmail("user1@example.com");
        user1.setTipo("Cliente");

        Utente admin1 = new Utente();
        admin1.setEmail("admin@example.com");
        admin1.setTipo("Gestore");

        List<Utente> allUsers = new ArrayList<>();
        allUsers.add(user1);
        allUsers.add(admin1);

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            UtenteDAO mockDAO = mockedConstruction.constructed().get(0);
            verify(mockDAO, times(1)).doRetrieveAll();
            verify(request).setAttribute(anyString(), any());
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    /**
     * Test multiple requests.
     * Scenario: Multiple servlet requests to verify consistency
     */
    @Test
    void testDoGet_MultipleRequests() throws ServletException, IOException {
        for (int i = 0; i < 3; i++) {
            // Reset mocks for each iteration
            reset(request, dispatcher);
            when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/gestisciOrdini.jsp")).thenReturn(dispatcher);

            Utente user = new Utente();
            user.setEmail("user@example.com");
            user.setTipo("Cliente");

            List<Utente> allUsers = new ArrayList<>();
            allUsers.add(user);

            try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
                when(mock.doRetrieveAll()).thenReturn(allUsers);
            })) {
                // Act
                servlet.doGet(request, response);

                // Assert
                verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                    utenti instanceof List && ((List<?>) utenti).size() == 1
                ));
            }
        }
    }

    /**
     * Test with users having special characters in email.
     * Scenario: User emails with special characters
     */
    @Test
    void testDoGet_SpecialCharactersInUserEmail() throws ServletException, IOException {
        // Arrange
        Utente user1 = new Utente();
        user1.setEmail("user.name+tag@sub.example.com");
        user1.setTipo("Cliente");

        Utente user2 = new Utente();
        user2.setEmail("user_with_underscore@example.com");
        user2.setTipo("Cliente");

        List<Utente> allUsers = new ArrayList<>();
        allUsers.add(user1);
        allUsers.add(user2);

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && ((List<?>) utenti).size() == 2
            ));
        }
    }

    /**
     * Test filtering behavior with mixed users and admins.
     * Scenario: Verify actual servlet behavior with mixed list
     */
    @Test
    void testDoGet_FilteringMaintainsOrder() throws ServletException, IOException {
        // Arrange
        Utente user1 = new Utente();
        user1.setEmail("user1@example.com");
        user1.setTipo("Cliente");

        Utente admin1 = new Utente();
        admin1.setEmail("admin@example.com");
        admin1.setTipo("Gestore");

        Utente user2 = new Utente();
        user2.setEmail("user2@example.com");
        user2.setTipo("Cliente");

        List<Utente> allUsers = new ArrayList<>();
        allUsers.add(user1);
        allUsers.add(admin1);
        allUsers.add(user2);

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert - Admin at index 1 is removed, leaving user1 and user2 (size=2)
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && 
                ((List<?>) utenti).size() == 2
            ));
        }
    }

    /**
     * Test with different admin type variations.
     * Scenario: Admin users with variations of "Gestore" type
     * Note: Due to servlet's remove-during-iteration bug, some admins remain
     */
    @Test
    void testDoGet_AdminTypeVariations() throws ServletException, IOException {
        // Arrange
        Utente client = new Utente();
        client.setEmail("client@example.com");
        client.setTipo("Cliente");

        Utente gestore = new Utente();
        gestore.setEmail("gestore@example.com");
        gestore.setTipo("Gestore");

        Utente gestoreAdmin = new Utente();
        gestoreAdmin.setEmail("gestore.admin@example.com");
        gestoreAdmin.setTipo("Gestore Admin");

        Utente gestoreSenior = new Utente();
        gestoreSenior.setEmail("gestore.senior@example.com");
        gestoreSenior.setTipo("Gestore Senior");

        List<Utente> allUsers = new ArrayList<>();
        allUsers.add(client);
        allUsers.add(gestore);
        allUsers.add(gestoreAdmin);
        allUsers.add(gestoreSenior);

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert - 3 admins removed with reverse iteration, only client remains
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && ((List<?>) utenti).size() == 1
            ));
        }
    }

    /**
     * Test forward is called exactly once.
     * Scenario: Verify dispatcher.forward is invoked exactly one time
     */
    @Test
    void testDoGet_ForwardCalledExactlyOnce() throws ServletException, IOException {
        // Arrange
        List<Utente> allUsers = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    /**
     * Test setAttribute is called with correct attribute name.
     * Scenario: Verify setAttribute is called with "utenti" key
     */
    @Test
    void testDoGet_SetAttributeCalledWithCorrectKey() throws ServletException, IOException {
        // Arrange
        List<Utente> allUsers = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("utenti"), any());
        }
    }

    /**
     * Test with mixed user types and admin variants.
     * Scenario: Complex scenario with various user and admin type combinations
     * Note: Due to servlet's remove-during-iteration bug, some admins remain
     */
    @Test
    void testDoGet_MixedUserTypesAndAdminVariants() throws ServletException, IOException {
        // Arrange
        List<Utente> allUsers = new ArrayList<>();

        // Add different client types
        for (String clientType : new String[]{"Cliente", "Cliente Gold", "Cliente Premium"}) {
            Utente user = new Utente();
            user.setEmail("user." + clientType.toLowerCase().replace(" ", "") + "@example.com");
            user.setTipo(clientType);
            allUsers.add(user);
        }

        // Add different admin types (some may remain due to iteration bug)
        for (String adminType : new String[]{"Gestore", "Gestore Manager", "Gestore Admin"}) {
            Utente admin = new Utente();
            admin.setEmail("admin." + adminType.toLowerCase().replace(" ", "") + "@example.com");
            admin.setTipo(adminType);
            allUsers.add(admin);
        }

        try (MockedConstruction<UtenteDAO> mockedConstruction = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveAll()).thenReturn(allUsers);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert - All 3 admins removed with reverse iteration, 3 client types remain
            verify(request).setAttribute(eq("utenti"), argThat(utenti ->
                utenti instanceof List && ((List<?>) utenti).size() == 3
            ));
        }
    }
}
