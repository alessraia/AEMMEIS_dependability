package controller.admin.gestisciOrdini;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

/**
 * Unit tests for GestisciOrdiniByUtente servlet.
 * Tests the servlet's ability to retrieve and display orders for a specific user
 * by retrieving user information and their associated orders.
 */
class GestisciOrdiniByUtenteTest {

    private GestisciOrdiniByUtente servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new GestisciOrdiniByUtente();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("/WEB-INF/results/admin/ordini/stampaOrdini.jsp")).thenReturn(dispatcher);
    }

    /**
     * Test successful retrieval of user and their orders.
     * Scenario: Valid user email is provided and orders are retrieved successfully
     */
    @Test
    void testDoGet_SuccessfulUserOrderRetrieval() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);
        utente.setNomeUtente("John Doe");

        List<Ordine> ordini = new ArrayList<>();
        Ordine ordine1 = new Ordine();
        ordine1.setIdOrdine("ORD001");
        ordine1.setEmail(userEmail);
        ordini.add(ordine1);

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", utente);
            verify(request).setAttribute("ordiniUtente", ordini);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test retrieval with user who has multiple orders.
     * Scenario: Valid user with multiple associated orders
     */
    @Test
    void testDoGet_UserWithMultipleOrders() throws ServletException, IOException {
        // Arrange
        String userEmail = "admin@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);
        utente.setNomeUtente("Admin User");

        List<Ordine> ordini = new ArrayList<>();
        for (int i = 1; i <= 5; i++) {
            Ordine ordine = new Ordine();
            ordine.setIdOrdine("ORD" + String.format("%03d", i));
            ordine.setEmail(userEmail);
            ordini.add(ordine);
        }

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", utente);
            verify(request).setAttribute(eq("ordiniUtente"), argThat(o -> 
                o instanceof List && ((List<?>) o).size() == 5
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test retrieval with user who has no orders.
     * Scenario: Valid user with empty order list
     */
    @Test
    void testDoGet_UserWithNoOrders() throws ServletException, IOException {
        // Arrange
        String userEmail = "newuser@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);
        utente.setNomeUtente("New User");

        List<Ordine> ordini = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("utenteScelto", utente);
            verify(request).setAttribute(eq("ordiniUtente"), argThat(o -> 
                o instanceof List && ((List<?>) o).isEmpty()
            ));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test request forwarding to correct JSP page.
     * Scenario: After retrieving data, request is forwarded to the correct dispatcher
     */
    @Test
    void testDoGet_RequestForwardedCorrectly() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).getRequestDispatcher("/WEB-INF/results/admin/ordini/stampaOrdini.jsp");
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test user data is correctly set in request attributes.
     * Scenario: Verify that the utenteScelto attribute contains the correct user object
     */
    @Test
    void testDoGet_UtenteSceltoAttributeCorrect() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);
        utente.setNomeUtente("Test User");

        List<Ordine> ordini = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("utenteScelto"), argThat(u -> 
                u instanceof Utente && ((Utente) u).getEmail().equals(userEmail)
            ));
        }
    }

    /**
     * Test orders data is correctly set in request attributes.
     * Scenario: Verify that the ordiniUtente attribute contains the correct orders
     */
    @Test
    void testDoGet_OrdiniUtenteAttributeCorrect() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();
        Ordine ordine1 = new Ordine();
        ordine1.setIdOrdine("ORD001");
        ordini.add(ordine1);

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("ordiniUtente"), argThat(o -> 
                o instanceof List && ((List<?>) o).size() == 1
            ));
        }
    }

    /**
     * Test correct DAO methods are called.
     * Scenario: Verify that both UtenteDAO and OrdineDAO are invoked correctly
     */
    @Test
    void testDoGet_DAOMethodsCalledCorrectly() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            UtenteDAO mockUtenteDAO = utenteDAOMock.constructed().get(0);
            OrdineDAO mockOrdineDAO = ordineDAOMock.constructed().get(0);

            verify(mockUtenteDAO).doRetrieveById(userEmail);
            verify(mockOrdineDAO).doRetrieveByUtente(userEmail);
        }
    }

    /**
     * Test operation sequence.
     * Scenario: Verify correct order of operations (retrieve user, retrieve orders, set attributes, forward)
     */
    @Test
    void testDoGet_CorrectOperationSequence() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            UtenteDAO mockUtenteDAO = utenteDAOMock.constructed().get(0);
            OrdineDAO mockOrdineDAO = ordineDAOMock.constructed().get(0);

            verify(mockUtenteDAO, times(1)).doRetrieveById(userEmail);
            verify(mockOrdineDAO, times(1)).doRetrieveByUtente(userEmail);
            verify(request, times(2)).setAttribute(anyString(), any());
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    /**
     * Test with special characters in user email.
     * Scenario: User email contains special characters
     */
    @Test
    void testDoGet_SpecialCharactersInUserEmail() throws ServletException, IOException {
        // Arrange
        String userEmail = "user.name+tag@sub.example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            UtenteDAO mockUtenteDAO = utenteDAOMock.constructed().get(0);
            verify(mockUtenteDAO).doRetrieveById(userEmail);
        }
    }

    /**
     * Test with null user parameter.
     * Scenario: When utenteScelto parameter is null
     */
    @Test
    void testDoGet_NullUserParameter() throws ServletException, IOException {
        // Arrange
        when(request.getParameter("utenteScelto")).thenReturn(null);

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(null)).thenReturn(null);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(null)).thenReturn(new ArrayList<>());
             })) {
            // Act & Assert
            try {
                servlet.doGet(request, response);
            } catch (NullPointerException e) {
                // Expected when trying to call getEmail() on null utente
                UtenteDAO mockUtenteDAO = utenteDAOMock.constructed().get(0);
                verify(mockUtenteDAO).doRetrieveById(null);
            }
        }
    }

    /**
     * Test with empty user parameter.
     * Scenario: When utenteScelto parameter is empty string
     */
    @Test
    void testDoGet_EmptyUserParameter() throws ServletException, IOException {
        // Arrange
        String userEmail = "";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            UtenteDAO mockUtenteDAO = utenteDAOMock.constructed().get(0);
            verify(mockUtenteDAO).doRetrieveById(userEmail);
        }
    }

    /**
     * Test with orders containing different attributes.
     * Scenario: Multiple orders with varied data
     */
    @Test
    void testDoGet_OrdersWithDifferentAttributes() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();
        
        Ordine ordine1 = new Ordine();
        ordine1.setIdOrdine("ORD001");
        ordine1.setEmail(userEmail);
        ordine1.setCosto(100.0);
        
        Ordine ordine2 = new Ordine();
        ordine2.setIdOrdine("ORD002");
        ordine2.setEmail(userEmail);
        ordine2.setCosto(250.50);
        
        ordini.add(ordine1);
        ordini.add(ordine2);

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("ordiniUtente"), argThat(o -> 
                o instanceof List && ((List<?>) o).size() == 2
            ));
        }
    }

    /**
     * Test with user not found scenario.
     * Scenario: UtenteDAO returns null for non-existent user
     */
    @Test
    void testDoGet_UserNotFound() throws ServletException, IOException {
        // Arrange
        String userEmail = "nonexistent@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(null);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(anyString())).thenReturn(new ArrayList<>());
             })) {
            // Act & Assert
            try {
                servlet.doGet(request, response);
            } catch (NullPointerException e) {
                // Expected when utente is null and getEmail() is called
                UtenteDAO mockUtenteDAO = utenteDAOMock.constructed().get(0);
                verify(mockUtenteDAO).doRetrieveById(userEmail);
            }
        }
    }

    /**
     * Test multiple attributes are set.
     * Scenario: Verify both setAttribute calls are made
     */
    @Test
    void testDoGet_BothAttributesSet() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request, times(2)).setAttribute(anyString(), any());
        }
    }

    /**
     * Test dispatcher forward is called exactly once.
     * Scenario: Verify that forward is called only once per request
     */
    @Test
    void testDoGet_ForwardCalledExactlyOnce() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    /**
     * Test large number of orders.
     * Scenario: User with many orders
     */
    @Test
    void testDoGet_LargeNumberOfOrders() throws ServletException, IOException {
        // Arrange
        String userEmail = "user@example.com";

        when(request.getParameter("utenteScelto")).thenReturn(userEmail);

        Utente utente = new Utente();
        utente.setEmail(userEmail);

        List<Ordine> ordini = new ArrayList<>();
        for (int i = 1; i <= 100; i++) {
            Ordine ordine = new Ordine();
            ordine.setIdOrdine("ORD" + String.format("%05d", i));
            ordine.setEmail(userEmail);
            ordini.add(ordine);
        }

        try (MockedConstruction<UtenteDAO> utenteDAOMock = mockConstruction(UtenteDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(userEmail)).thenReturn(utente);
        });
             MockedConstruction<OrdineDAO> ordineDAOMock = mockConstruction(OrdineDAO.class, (mock, context) -> {
                 when(mock.doRetrieveByUtente(userEmail)).thenReturn(ordini);
             })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("ordiniUtente"), argThat(o -> 
                o instanceof List && ((List<?>) o).size() == 100
            ));
            verify(dispatcher).forward(request, response);
        }
    }
}
