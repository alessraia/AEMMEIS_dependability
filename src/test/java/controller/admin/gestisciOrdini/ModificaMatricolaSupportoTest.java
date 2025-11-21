package controller.admin.gestisciOrdini;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.gestoreService.Gestore;
import model.gestoreService.GestoreDAO;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for ModificaMatricolaSupporto servlet.
 * Tests the servlet's ability to modify support staff assignment for orders,
 * including retrieval of users, orders, staff lists, and removal of unavailable staff.
 */
class ModificaMatricolaSupportoTest {
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;
    private ModificaMatricolaSupporto servlet;

    @BeforeEach
    void setUp() {
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
        servlet = new ModificaMatricolaSupporto();
    }

    /**
     * Helper method to create a Gestore with matricola and stipendio.
     */
    private Gestore createGestore(String matricola, double stipendio) {
        Gestore gestore = new Gestore();
        gestore.setMatricola(matricola);
        gestore.setStipendio(stipendio);
        return gestore;
    }

    /**
     * Helper method to create a Utente with email and name.
     */
    private Utente createUtente(String email, String nome) {
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setNomeUtente(nome);
        return utente;
    }

    /**
     * Helper method to create an Ordine with ID.
     */
    private Ordine createOrdine(String ordineID) {
        Ordine ordine = new Ordine();
        ordine.setIdOrdine(ordineID);
        return ordine;
    }

    /**
     * Test basic functionality: retrieve user, order, and staff list.
     * Scenario: All DAOs work correctly and attributes are set
     */
    @Test
    void testDoGet_BasicFunctionality() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT001");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT002", 1500));
        gestori.add(createGestore("MAT003", 1600));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("ordineAttuale"), eq(ordine));
            verify(request).setAttribute(eq("utenteScelto"), eq(utente));
            verify(request).setAttribute(eq("gestori"), argThat(list -> list instanceof List && ((List<?>) list).size() == 2));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test current staff removal: staff with current matricola is removed.
     * Scenario: Current staff (MAT001) is removed from list, others remain
     */
    @Test
    void testDoGet_CurrentMatricolaRemoved() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT001");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT001", 1500));
        gestori.add(createGestore("MAT002", 1600));
        gestori.add(createGestore("MAT003", 1700));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - Only 2 gestori remain (MAT001 removed)
            verify(request).setAttribute(eq("gestori"), argThat(list ->
                list instanceof List && ((List<?>) list).size() == 2
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test case-insensitive matching: matricola comparison is case-insensitive.
     * Scenario: MAT001 matches mat001 due to equalsIgnoreCase
     */
    @Test
    void testDoGet_CaseInsensitiveMatching() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("mat001");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT001", 1500));
        gestori.add(createGestore("MAT002", 1600));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - Only 1 gestore remains (mat001 matches MAT001)
            verify(request).setAttribute(eq("gestori"), argThat(list ->
                list instanceof List && ((List<?>) list).size() == 1
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test empty staff list: no gestori are available.
     * Scenario: DAO returns empty list, result should remain empty
     */
    @Test
    void testDoGet_EmptyStaffList() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT001");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("gestori"), argThat(list ->
                list instanceof List && ((List<?>) list).isEmpty()
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test multiple gestori with same matricola: only first match is removed.
     * Scenario: Multiple gestori with same matricola (data anomaly), only first is removed
     */
    @Test
    void testDoGet_MultipleGestoriWithSameMatricola() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT001");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT001", 1500));
        gestori.add(createGestore("MAT001", 1550));
        gestori.add(createGestore("MAT002", 1600));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - Only 2 gestori remain (first MAT001 removed, second MAT001 remains)
            verify(request).setAttribute(eq("gestori"), argThat(list ->
                list instanceof List && ((List<?>) list).size() == 2
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test non-existent matricola: no removal occurs when matricola not found.
     * Scenario: Current matricola is not in the list, all gestori remain
     */
    @Test
    void testDoGet_NonExistentMatricola() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT999");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT001", 1500));
        gestori.add(createGestore("MAT002", 1600));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - All gestori remain (no match found)
            verify(request).setAttribute(eq("gestori"), argThat(list ->
                list instanceof List && ((List<?>) list).size() == 2
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test large staff list: removal works correctly with many gestori.
     * Scenario: Large list with many gestori, one is removed
     */
    @Test
    void testDoGet_LargeStaffList() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT025");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();
        for (int i = 1; i <= 50; i++) {
            gestori.add(createGestore("MAT" + String.format("%03d", i), 1500 + i));
        }

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - 49 gestori remain (MAT025 removed)
            verify(request).setAttribute(eq("gestori"), argThat(list ->
                list instanceof List && ((List<?>) list).size() == 49
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test null user parameter: handles null email gracefully.
     * Scenario: utenteScelto parameter is null
     */
    @Test
    void testDoGet_NullUserParameter() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn(null);
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT001");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT001", 1500));
        gestori.add(createGestore("MAT002", 1600));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById(null)).thenReturn(null));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - Servlet continues and sets attributes
            verify(request).setAttribute(eq("utenteScelto"), isNull());
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test null order parameter: handles missing order.
     * Scenario: ordineID parameter is null
     */
    @Test
    void testDoGet_NullOrderParameter() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT001");
        when(request.getParameter("ordineID")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT001", 1500));
        gestori.add(createGestore("MAT002", 1600));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById(null)).thenReturn(null));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - Servlet continues with null ordine
            verify(request).setAttribute(eq("ordineAttuale"), isNull());
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test null matricola parameter: no removal occurs.
     * Scenario: matricolaAttuale parameter is null
     */
    @Test
    void testDoGet_NullMatricolaParameter() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn(null);
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT001", 1500));
        gestori.add(createGestore("MAT002", 1600));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - All gestori remain (no match with null)
            verify(request).setAttribute(eq("gestori"), argThat(list ->
                list instanceof List && ((List<?>) list).size() == 2
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test empty string parameters: treats empty strings as regular values.
     * Scenario: Parameters are empty strings
     */
    @Test
    void testDoGet_EmptyStringParameters() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("");
        when(request.getParameter("matricolaAttuale")).thenReturn("");
        when(request.getParameter("ordineID")).thenReturn("");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = new Utente();
        Ordine ordine = new Ordine();
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT001", 1500));
        gestori.add(createGestore("", 1600));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - Empty string gestore is removed
            verify(request).setAttribute(eq("gestori"), argThat(list ->
                list instanceof List && ((List<?>) list).size() == 1
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test special characters in matricola: handles special characters correctly.
     * Scenario: Matricola contains special characters and is matched correctly
     */
    @Test
    void testDoGet_SpecialCharactersInMatricola() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT-001/A");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();
        gestori.add(createGestore("MAT-001/A", 1500));
        gestori.add(createGestore("MAT002", 1600));

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - Gestore with special characters is removed
            verify(request).setAttribute(eq("gestori"), argThat(list ->
                list instanceof List && ((List<?>) list).size() == 1
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test dispatcher: verify correct JSP path and forward is called exactly once.
     * Scenario: Dispatcher is called with correct path and forward is invoked once
     */
    @Test
    void testDoGet_DispatcherPathAndForward() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn("user@example.com");
        when(request.getParameter("matricolaAttuale")).thenReturn("MAT001");
        when(request.getParameter("ordineID")).thenReturn("ORD123");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp")).thenReturn(dispatcher);

        Utente utente = createUtente("user@example.com", "John Doe");
        Ordine ordine = createOrdine("ORD123");
        List<Gestore> gestori = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> mockUtenteDAO = mockConstruction(UtenteDAO.class,
                (mock, context) -> when(mock.doRetrieveById("user@example.com")).thenReturn(utente));
             MockedConstruction<OrdineDAO> mockOrdineDAO = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD123")).thenReturn(ordine));
             MockedConstruction<GestoreDAO> mockGestoreDAO = mockConstruction(GestoreDAO.class,
                (mock, context) -> when(mock.doRetrivedAll()).thenReturn(gestori))) {

            // Act
            servlet.doGet(request, response);

            // Assert - Verify correct path and forward called exactly once
            verify(request).getRequestDispatcher("/WEB-INF/results/admin/ordini/modificaMatricola.jsp");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }
}
